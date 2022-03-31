#include <functional>
#include <map>
#include <optional>
#include <vector>
#include <tao/pegtl.hpp>

#pragma once


namespace Gold
{

template<typename T>
using sptr = std::shared_ptr<T>;

template<typename T>
using uptr = std::unique_ptr<T>;

template<typename T>
using opt = std::optional<T>;

class EvaluationContext;
class Object;
class Serializer;
class Deserializer;
struct Expr;
struct Binding;

using ExprPtr = uptr<Expr>;
using BindingPtr = uptr<Binding>;
using Namespace = std::map<std::string, Object>;
extern Namespace builtins;

enum class BinaryOperator;
enum class UnaryOperator;
struct CollectionElement;
struct ListElement;
struct MapElement;
struct ListBinding;
struct MapBinding;
struct MapBindingEntry;
struct BlockBindingElement;

struct Source {
    size_t byte;
    size_t line;
    size_t column;
};

struct InternalException: public std::exception {
    std::string msg;
    InternalException() : msg("an internal error happend - please report") {}
    InternalException(std::string s) : msg(s) {}

    const char* what() const noexcept {
        return msg.c_str();
    }
};

struct EvalException: public std::exception {
    std::vector<Source> positions;
    std::vector<std::string> lines;
    std::string reason;
    opt<std::string> message;

    EvalException() : reason("") {}
    EvalException(std::string_view reason) : reason(reason) {}
    EvalException(Source src, std::string reason) : positions({src}), reason(reason) {}

    void tag_position(Source, bool = false) noexcept;
    void tag_lines(std::function<std::string_view(Source&)>) noexcept;

    const char* what() const noexcept;
};

bool analyze_grammar();
void debug_parse(std::string input);
void debug_parse_tree(std::string input);

}
