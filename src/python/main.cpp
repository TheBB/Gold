#include <sstream>

#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include "gold.hpp"

using namespace Gold;
namespace py = pybind11;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


namespace pybind11 { namespace detail {
    template <> struct type_caster<Object> {
        PYBIND11_TYPE_CASTER(Object, _("Object"));

    public:

        bool load(handle src, bool convert) {
            if (py::isinstance<py::none>(src)) {
                value = Object::null();
                return true;
            }

            if (py::isinstance<py::bool_>(src)) {
                auto caster = type_caster<Object::Boolean>();
                if (!caster.load(src, convert))
                    return false;
                value = Object::boolean((Object::Boolean)caster);
                return true;
            }

            if (py::isinstance<py::int_>(src)) {
                auto caster = type_caster<Object::Integer>();
                if (!caster.load(src, convert))
                    return false;
                value = Object::integer((Object::Integer)caster);
                return true;
            }

            if (py::isinstance<py::float_>(src)) {
                auto caster = type_caster<Object::Floating>();
                if (!caster.load(src, convert))
                    return false;
                value = Object::floating((Object::Floating)caster);
                return true;
            }

            if (py::isinstance<py::str>(src)) {
                auto caster = type_caster<Object::String>();
                if (!caster.load(src, convert))
                    return false;
                value = Object::string((Object::String)caster);
                return true;
            }

            if (py::isinstance<py::list>(src)) {
                auto caster = type_caster<Object::ListT>();
                if (!caster.load(src, convert))
                    return false;
                value = Object::list((Object::ListT)caster);
                return true;
            }

            if (py::isinstance<py::dict>(src)) {
                auto caster = type_caster<Object::MapT>();
                if (!caster.load(src, convert))
                    return false;
                value = Object::map((Object::MapT)caster);
                return true;
            }

            auto caster = type_caster_base<Object>();
            if (!caster.load(src, convert))
                return false;
            value = (Object&) caster;
            return true;
        }

        static handle cast(Object src, return_value_policy policy, handle parent) {
            return std::visit(overloaded {
                [](Object::Null) -> handle {
                    Py_INCREF(Py_None);
                    return Py_None;
                },
                [policy, parent](Object::Boolean x) {
                    return type_caster<Object::Boolean>::cast(x, policy, parent);
                },
                [policy, parent](Object::Integer x) {
                    return type_caster<Object::Integer>::cast(x, policy, parent);
                },
                [policy, parent](Object::Floating x) {
                    return type_caster<Object::Floating>::cast(x, policy, parent);
                },
                [policy, parent](Object::String x) {
                    return type_caster<Object::String>::cast(x, policy, parent);
                },
                [policy, parent](Object::List x) {
                    return type_caster<Object::ListT>::cast(*x, policy, parent);
                },
                [policy, parent](Object::Map x) {
                    return type_caster<Object::MapT>::cast(*x, policy, parent);
                },
                [src, policy, parent](auto&&) -> handle {
                    return type_caster_base<Object>::cast(src, policy, parent);
                }
            }, src.data());
        }
    };
}}


class PyLibFinder: public LibFinder {
public:
    using LibFinder::LibFinder;
    std::optional<Object> find(const std::string& path) const override {
        PYBIND11_OVERRIDE_PURE(std::optional<Object>, LibFinder, find, path);
    }
};


PYBIND11_MODULE(pygold, m) {
    py::register_exception<EvalException>(m, "EvalException");
    py::register_exception<InternalException>(m, "InternalException");
    py::class_<EvaluationContext>(m, "EvaluationContext")
        .def(py::init<>())
        .def("append_libfinder", &EvaluationContext::append_libfinder);
    py::class_<LibFinder, PyLibFinder, std::shared_ptr<LibFinder>>(m, "LibFinder")
        .def(py::init<>())
        .def("find", &LibFinder::find);
    py::class_<Object>(m, "Object")
        .def("__call__", [](Object& obj, py::args args) {
            py::detail::type_caster<std::vector<Object>> caster;
            if (!caster.load(args, false))
                throw pybind11::type_error("incompatible function arguments");
            EvaluationContext ctx;
            return obj(ctx, (std::vector<Object>&)caster);
        });
    m.def("evaluate_string", py::overload_cast<std::string>(&evaluate_string));
    m.def("evaluate_string", py::overload_cast<EvaluationContext&, std::string>(&evaluate_string));
    m.def("evaluate_file", py::overload_cast<std::string>(&evaluate_file));
    m.def("evaluate_file", py::overload_cast<EvaluationContext&, std::string>(&evaluate_file));
}
