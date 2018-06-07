#include "CopyElision.h"
#include "IREquality.h"
#include "IRMutator.h"
#include "Func.h"
#include "FindCalls.h"
#include "Schedule.h"

namespace Halide {
namespace Internal {

using std::map;
using std::set;
using std::string;
using std::vector;

namespace {

/** If function 'f' operation only involves pointwise copy from another
  * function, return the name of the function from which it copies from.
  * If the function being copied from is a tuple, we have to ensure that 'f'
  * copies the whole tuple and not only some of the tuple values; otherwise,
  * treat it as non pointwise copies. For non pointwise copy or if 'f' has
  * update definitions or is an extern function, return an empty string.
  */
string get_pointwise_copy_producer(const Function &f,
                                   const map<string, int> &num_callers) {
    if (f.has_update_definition()) {
        return "";
    }

    if (f.has_extern_definition() &&
        (f.extern_function_name() == "halide_buffer_copy")) {
        // TODO(psuriana): Check if this extern function is actually a
        // a buffer copy
        // TODO(psuriana): How do you handle Tuple for buffer copy?
        string prod;
        for (const ExternFuncArgument &arg : f.extern_arguments()) {
            if (arg.is_func()) {
                Function g(arg.func);
                if (!prod.empty() && (prod != g.name())) {
                    debug(0) << "...Extern function \"" << f.name() << "\" copies multiple "
                             << "functions: \"" << prod << "\" and \""
                             << g.name() << "\"\n";
                    return "";
                }
                prod = g.name();
            }
        }
        if (!prod.empty()) {
            debug(0) << "...Found halide_buffer_copy -> " << print_function(f) << "\n";
        }
        return prod;
    }

    string prod;
    for (int i = 0; i < (int)f.values().size(); ++i) {
        const Expr &val = f.values()[i];
        if (const Call *call = val.as<Call>()) {
            if (call->call_type == Call::Halide) {
                // Check if it is a pointwise copy. For tuple, check if 'f'
                // copies the whole tuple values.
                if (!prod.empty() && (prod != call->name)) {
                    debug(0) << "...Function \"" << f.name() << "\" calls multiple "
                             << "functions: \"" << prod << "\" and \""
                             << call->name << "\"\n";
                    return "";
                }
                prod = call->name;

                // Check if only 'f' calls 'prod'
                const auto &iter = num_callers.find(prod);
                if ((iter != num_callers.end()) && (iter->second > 1)) {
                    debug(0) << "...Function \"" << f.name() << "\" is pointwise copies but \""
                             << prod << "\" has multiple callers\n";
                    return "";
                }

                Function prod_f = Function(call->func);
                if (f.dimensions() != prod_f.dimensions()) {
                    debug(0) << "...Function \"" << f.name() << "\" does not call "
                             << "the whole tuple values of function \""
                             << prod_f.name() << "\"\n";
                    return "";
                }

                if (i != call->value_index) {
                    debug(0) << "...Function \"" << f.name() << "\" calls "
                             << prod_f.name() << "[" << call->value_index
                             << "] at value index " << i << "\n";
                    return "";
                }

                for (int j = 0; j < f.dimensions(); ++j) {
                    // Check if the call args are equivalent for both the
                    // RHS ('f') and LHS ('prod_f').
                    // TODO(psuriana): Handle case for copy with some index shifting
                    if (!equal(f.args()[j], prod_f.args()[j])) {
                        debug(0) << "At arg " << j << ", " << f.name() << "("
                                 << f.args()[i] << ") != " << prod_f.name()
                                 << "[" << call->value_index << "]("
                                 << prod_f.args()[j] << ")\n";
                        return "";
                    }
                }
            }
        } else if (!prod.empty()) {
            debug(0) << "...Function \"" << f.name() << "\" does not call "
                     << "the whole tuple values of function \""
                     << prod << "\" or is not a simple copy\n";
            return "";
        }
    }

    if (!prod.empty()) {
        debug(0) << "...Found pointwise copy -> " << print_function(f) << "\n";
    }
    return prod;
}

} // anonymous namespace

string print_function(const Function &f) {
    std::ostringstream stream;
    stream << f.name() << "(";
    for (int i = 0; i < f.dimensions(); ++i) {
        stream << f.args()[i];
        if (i != f.dimensions()-1) {
            stream << ", ";
        }
    }
    stream << ") = ";

    if (f.has_extern_definition()) {
        vector<Expr> extern_call_args;
        const vector<ExternFuncArgument> &args = f.extern_arguments();
        for (const ExternFuncArgument &arg : args) {
            if (arg.is_expr()) {
                extern_call_args.push_back(arg.expr);
            } else if (arg.is_func()) {
                Function input(arg.func);
                LoopLevel store_level = input.schedule().store_level().lock();
                LoopLevel compute_level = input.schedule().compute_level().lock();
                if (store_level == compute_level) {
                    for (int k = 0; k < input.outputs(); k++) {
                        string buf_name = input.name();
                        if (input.outputs() > 1) {
                            buf_name += "." + std::to_string(k);
                        }
                        buf_name += ".buffer";
                        Expr buffer = Variable::make(type_of<struct halide_buffer_t *>(), buf_name);
                        extern_call_args.push_back(buffer);
                    }
                } else {
                    for (int k = 0; k < input.outputs(); k++) {
                        string buf_name = input.name() + "." + std::to_string(k) + ".tmp_buffer";
                        extern_call_args.push_back(Variable::make(type_of<struct halide_buffer_t *>(), buf_name));
                    }
                }
            } else if (arg.is_buffer()) {
                Buffer<> b = arg.buffer;
                Parameter p(b.type(), true, b.dimensions(), b.name());
                p.set_buffer(b);
                Expr buf = Variable::make(type_of<struct halide_buffer_t *>(), b.name() + ".buffer", p);
                extern_call_args.push_back(buf);
            } else if (arg.is_image_param()) {
                Parameter p = arg.image_param;
                Expr buf = Variable::make(type_of<struct halide_buffer_t *>(), p.name() + ".buffer", p);
                extern_call_args.push_back(buf);
            } else {
                internal_error << "Bad ExternFuncArgument type\n";
            }
        }
        Expr expr = f.make_call_to_extern_definition(extern_call_args, get_target_from_environment());
        stream << expr;
    } else {
        if (f.values().size() > 1) {
            stream << "{";
        }
        for (int i = 0; i < (int)f.values().size(); ++i) {
            stream << f.values()[i];
            if (i != (int)f.values().size()-1) {
                stream << ", ";
            }
        }
        if (f.values().size() > 1) {
            stream << "}";
        }
    }
    return stream.str();
}

/** Return all pairs of functions which operation only involves pointwise copy
  * of another function and the function from which it copies from. Ignore
  * functions that have updates or are extern functions. */
vector<CopyPair> get_pointwise_copies(const map<string, Function> &env) {
    // We should only consider the case when the function only has 1 caller
    map<string, int> num_callers;
    for (const auto &caller : env) {
        for (const auto &callee : find_direct_calls(caller.second)) {
            num_callers[callee.first] += 1;
        }
    }

    // TODO(psuriana): Need to figure out that the copies are on the same device;
    // otherwise, it shouldn't have been optimized away

    vector<CopyPair> pointwise_copies;
    for (const auto &iter : env) {
        // Ignore inlined function
        // TODO(psuriana): how should we handle the case when either the producer
        // or the consumer of the copy-pair is inlined?
        if (iter.second.schedule().compute_level().is_inlined()) {
            continue;
        }
        string copied_from = get_pointwise_copy_producer(iter.second, num_callers);
        if (!copied_from.empty()) {
            pointwise_copies.push_back({copied_from, iter.first});
        }
    }
    return pointwise_copies;
}

void copy_elision_test() {
    /*{
        Func tile("tile"), output("output"), f("f"), g("g"), h("h"), in("in");
        Var x("x"), y("y");

        f(x, y) = x + y;
        g(x, y) = x - y;
        h(x, y) = g(x, y);
        in(x, y) = h(x, y);
        tile(x, y) = {f(x, y), g(x, y)};
        output(x, y) = tile(y, x);

        map<string, Function> env;
        env.emplace(tile.name(), tile.function());
        env.emplace(output.name(), output.function());
        env.emplace(f.name(), f.function());
        env.emplace(g.name(), g.function());
        env.emplace(h.name(), h.function());
        env.emplace(in.name(), in.function());

        vector<CopyPair> result = get_pointwise_copies(env);
        debug(0) << "\nPointwise copies:\n";
        for (const auto &p : result) {
            debug(0) << "prod: " << p.prod << " -> cons: " << p.cons << "\n";
            debug(0) << "\t\tcons: " << print_function(env.at(p.cons)) << "\n";
            debug(0) << "\t\tprod: " << print_function(env.at(p.prod)) << "\n\n";
        }
        debug(0) << "\n";
    }

    {
        Func input("input"), input_copy("input_copy"), work("work"), output("output"), output_copy("output_copy"), g("g");
        Var x("x"), y("y");

        input(x, y) = x + y;
        input_copy(x, y) = input(x, y);
        work(x, y) = input_copy(x, y) * 2;
        output(x, y) = work(x, y);
        output_copy(x, y) = output(x, y);

        output.copy_to_device();

        map<string, Function> env;
        env.emplace(input.name(), input.function());
        env.emplace(input_copy.name(), input_copy.function());
        env.emplace(work.name(), work.function());
        env.emplace(output.name(), output.function());
        env.emplace(output_copy.name(), output_copy.function());

        vector<CopyPair> result = get_pointwise_copies(env);
        debug(0) << "\nPointwise copies:\n";
        for (const auto &p : result) {
            debug(0) << "prod: " << p.prod << " -> cons: " << p.cons << "\n";
            debug(0) << "\t\tcons: " << print_function(env.at(p.cons)) << "\n";
            debug(0) << "\t\tprod: " << print_function(env.at(p.prod)) << "\n\n";
        }
        debug(0) << "\n";
    }*/

    std::cout << "Copy elision test passed" << std::endl;
}

}  // namespace Internal
}  // namespace Halide
