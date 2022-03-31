#include <cinttypes>

#include "gold.hpp"
#include "parsing.hpp"
#include "tree.hpp"


using namespace Gold;


Expr* Ast::root_expr() const {
    return expr().release();
}


Source Ast::source() const {
    return Source { begin.byte, begin.line, begin.column };
}


std::string_view Ast::string_view() const noexcept {
    return std::string_view( begin.data, end.data - begin.data );
}


std::string Ast::string() const {
    return std::string( begin.data, end.data );
}


ExprPtr Ast::expr() const {
    if (is_root())
        return children[0]->expr();
    return std::get<ExprN>(normalizer)(*this);
}


ExprPtr Ast::postfix(ExprPtr expr) const {
    return std::get<ModExprN>(normalizer)(*this, std::move(expr));
}


void Ast::funcall_arg(ExprPtr& expr) const {
    std::get<FuncallArgN>(normalizer)(*this, expr);
}


uptr<CollectionElement> Ast::collection_element() const {
    return std::get<CollectionEltN>(normalizer)(*this);
}


BinaryOperator Ast::binop() const {
    return std::get<BinaryOperator>(normalizer);
}


UnaryOperator Ast::unop() const {
    return std::get<UnaryOperator>(normalizer);
}


BindingPtr Ast::binding() const {
    return std::get<BindingN>(normalizer)(*this);
}


Block::BindingElement Ast::binding_element() const {
    return std::get<BlockBindingEltN>(normalizer)(*this);
}


void Ast::list_binding_entry(uptr<ListBinding>& binding) const {
    std::get<ListBindingEltN>(normalizer)(*this, binding);
}


void Ast::map_binding_entry(uptr<MapBinding>& binding) const {
    std::get<MapBindingEltN>(normalizer)(*this, binding);
}


MapBinding::Entry Ast::map_binding_leaf() const {
    return std::get<MapBindingLeafN>(normalizer)(*this);
}


template<typename T>
static std::string codepoint_as_string(T it, int nchars) {
    uint16_t codepoint = 0;
    for (int i = 0; i < nchars; i++) {
        codepoint *= 16;
        char s = it[i + 1];
        if ('A' <= s && s <= 'F')
            codepoint += s - 'A' + 10;
        else if ('a' <= s && s <= 'f')
            codepoint += s - 'a' + 10;
        else
            codepoint += s - '0';
    }

    if (codepoint < 128) {
        char a = codepoint & 0b0111'1111;
        return std::string{a};
    }
    else if (codepoint < 2048) {
        char a = ((codepoint & 0b0000'0111'1100'0000) >> 6) | 0b1100'0000;
        char b = ((codepoint & 0b0000'0000'0011'1111) >> 0) | 0b1000'0000;
        return std::string{a,b};
    }

    char a = ((codepoint & 0b1111'0000'0000'0000) >> 12) | 0b1110'0000;
    char b = ((codepoint & 0b0000'1111'1100'0000) >>  6) | 0b1000'0000;
    char c = ((codepoint & 0b0000'0000'0011'1111) >>  0) | 0b1000'0000;
    return std::string{a,b,c};
}


template<> void Ast::set_normalizer<Grammar::pattern::ident>() {
    normalizer = [](const Ast& ast) -> BindingPtr {
        return std::make_unique<IdentifierBinding>(ast.source(), ast.string());
    };
}


template<> void Ast::set_normalizer<Grammar::pattern::opt_slurp>() {
    normalizer = [](const Ast& ast, uptr<ListBinding>& binding) -> void {
        binding->slurp = true;
        if (!ast.children.empty())
            binding->slurp_target = ast.children[0]->string();
    };
}

template<> void Ast::set_normalizer<Grammar::pattern::list::element>() {
    normalizer = [](const Ast& ast, uptr<ListBinding>& binding) -> void {
        auto element = ListBinding::Entry { ast.children[0]->binding() };
        if (ast.children.size() > 1)
            element.fallback = ast.children[1]->expr();
        binding->bindings.push_back(std::move(element));
    };
}


template<> void Ast::set_normalizer<Grammar::pattern::list::rule>() {
    normalizer = [](const Ast& ast) -> BindingPtr {
        auto list = std::make_unique<ListBinding>(ast.source());
        for (auto& c : ast.children)
            c->list_binding_entry(list);
        return list;
    };
}


template<> void Ast::set_normalizer<Grammar::func::posargs>() {
    set_normalizer<Grammar::pattern::list::rule>();
}


template<> void Ast::set_normalizer<Grammar::func::kwargs>() {
    set_normalizer<Grammar::pattern::map::rule>();
}


template<> void Ast::set_normalizer<Grammar::pattern::map::entry>() {
    normalizer = [](const Ast& ast) -> MapBinding::Entry {
        return MapBinding::Entry {
            ast.children[0]->string(),
            ast.children[1]->binding()
        };
    };
}


template<> void Ast::set_normalizer<Grammar::kwargs_only_func::kwargs>() {
    set_normalizer<Grammar::pattern::map::rule>();
}


template<> void Ast::set_normalizer<Grammar::pattern::map::single_entry>() {
    normalizer = [](const Ast& ast) -> MapBinding::Entry {
        auto name = ast.children[0]->string();
        return MapBinding::Entry {
            name,
            std::make_unique<IdentifierBinding>(ast.children[0]->source(), name)
        };
    };
}


template<> void Ast::set_normalizer<Grammar::pattern::def_slurp>() {
    normalizer = [](const Ast& ast, uptr<MapBinding>& binding) -> void {
        binding->slurp_target = ast.children[0]->string();
    };
}


template<> void Ast::set_normalizer<Grammar::pattern::map::element>() {
    normalizer = [](const Ast& ast, uptr<MapBinding>& binding) -> void {
        auto entry = ast.children[0]->map_binding_leaf();
        if (ast.children.size() > 1)
            entry.fallback = ast.children[1]->expr();
        binding->entries.push_back(std::move(entry));
    };
}


template<> void Ast::set_normalizer<Grammar::pattern::map::rule>() {
    is_mapbinding = true;
    normalizer = [](const Ast& ast) -> BindingPtr {
        auto map = std::make_unique<MapBinding>(ast.source());
        for (auto& c : ast.children)
            c->map_binding_entry(map);
        return map;
    };
}


template<> void Ast::set_normalizer<Grammar::file>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        return ast.children[0]->expr();
    };
}


template<> void Ast::set_normalizer<Grammar::boolean>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        return std::make_unique<Literal>(
            ast.source(),
            Object::boolean(ast.string_view() == "true")
        );
    };
}


template<> void Ast::set_normalizer<Grammar::keyword::Null>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        return std::make_unique<Literal>(ast.source(), Object::null());
    };
}


template<> void Ast::set_normalizer<Grammar::number::integer>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto str = ast.string();
        auto value = std::strtoimax(str.c_str(), nullptr, 10);
        return std::make_unique<Literal>(ast.source(), Object::integer(value));
    };
}


template<> void Ast::set_normalizer<Grammar::number::floating>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto value = std::stod(ast.string());
        return std::make_unique<Literal>(ast.source(), Object::floating(value));
    };
}


template<> void Ast::set_normalizer<Grammar::string::data>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto data = ast.string_view();
        std::stringstream builder;
        for (auto it = data.begin(); it != data.end(); it++) {
            if (*it == '\\') {
                it++;
                switch (*it) {
                case 'u': {
                    builder << codepoint_as_string(it, 4);
                    it += 4;
                    break;
                }
                case 'b': builder << '\b'; break;
                case 'f': builder << '\f'; break;
                case 'n': builder << '\n'; break;
                case 'r': builder << '\r'; break;
                case 't': builder << '\t'; break;
                default: builder << *it; break;
                }
            }
            else
                builder << *it;
        }
        return std::make_unique<Literal>(ast.source(), Object::string(builder.str()));
    };
}


template<> void Ast::set_normalizer<Grammar::string::interp>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto func = std::make_unique<Identifier>(ast.source(), "str");
        auto call = std::make_unique<FunCall>(ast.source(), std::move(func));
        call->elements.push_back(std::make_unique<SingletonListElement>(ast.children[0]->expr()));
        return call;
    };
}


template<> void Ast::set_normalizer<Grammar::string::post>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        if (ast.children.empty())
            return std::make_unique<Literal>(ast.source(), Object::string(""));
        auto it = ast.children.begin();
        auto expr = (*it)->expr();
        while (++it != ast.children.end()) {
            auto rhs = (*it)->expr();
            expr = std::make_unique<BinOp>((*it)->source(), std::move(expr), std::move(rhs), BinaryOperator::plus);
        }
        return expr;
    };
}


template<> void Ast::set_normalizer<Grammar::identifier>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        return std::make_unique<Identifier>(ast.source(), ast.string());
    };
}


template<> void Ast::set_normalizer<Grammar::list::splat>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<SplatElement>(ast.children[0]->expr());
    };
}


template<> void Ast::set_normalizer<Grammar::list::singleton>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<SingletonListElement>(ast.children[0]->expr());
    };
}


template<> void Ast::set_normalizer<Grammar::list::cond>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<CondCollectionElement>(ast.children[0]->expr(), ast.children[1]->collection_element());
    };
}


template<> void Ast::set_normalizer<Grammar::list::loop>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<LoopCollectionElement>(
            ast.children[0]->binding(),
            ast.children[1]->expr(),
            ast.children[2]->collection_element()
        );
    };
}


template<> void Ast::set_normalizer<Grammar::list::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto list = std::make_unique<List>(ast.source());
        for (auto& c : ast.children)
            list->elements.push_back(c->collection_element());
        return list;
    };
}


template<> void Ast::set_normalizer<Grammar::map::const_identifier>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        return std::make_unique<Literal>(ast.source(), Object::string(ast.string()));
    };
}


template<> void Ast::set_normalizer<Grammar::map::splat>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<SplatElement>(ast.children[0]->expr());
    };
}


template<> void Ast::set_normalizer<Grammar::map::entry>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<SingletonMapElement>(ast.children[0]->expr(), ast.children[1]->expr());
    };
}


template<> void Ast::set_normalizer<Grammar::map::cond>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<CondCollectionElement>(ast.children[0]->expr(), ast.children[1]->collection_element());
    };
}


template<> void Ast::set_normalizer<Grammar::map::loop>() {
    normalizer = [](const Ast& ast) -> uptr<CollectionElement> {
        return std::make_unique<LoopCollectionElement>(
            ast.children[0]->binding(),
            ast.children[1]->expr(),
            ast.children[2]->collection_element()
        );
    };
}


template<> void Ast::set_normalizer<Grammar::map::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto map = std::make_unique<Map>(ast.source());
        for (auto& c : ast.children)
            map->elements.push_back(c->collection_element());
        return map;
    };
}


template<> void Ast::set_normalizer<Grammar::block::binding>() {
    normalizer = [](const Ast& ast) -> Block::BindingElement {
        return Block::BindingElement {
            ast.children[0]->binding(),
            ast.children[1]->expr()
        };
    };
}


template<> void Ast::set_normalizer<Grammar::block::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto block = std::make_unique<Block>(ast.source());
        auto it = ast.children.begin();
        for (; it != ast.children.end() - 1; it++)
            block->bindings.push_back((*it)->binding_element());
        block->expression = (*it)->expr();
        return block;
    };
}


template<> void Ast::set_normalizer<Grammar::branch>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        return std::make_unique<Branch>(
            ast.source(),
            ast.children[0]->expr(),
            ast.children[1]->expr(),
            ast.children[2]->expr()
        );
    };
}


template<> void Ast::set_normalizer<Grammar::func::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto func = std::make_unique<Function>(ast.source());
        func->args = ast.children[0]->binding();
        if (ast.children.size() > 2) {
            func->kwargs = ast.children[1]->binding();
            func->expression = ast.children[2]->expr();
        }
        else {
            func->kwargs = std::make_shared<MapBinding>(Source {0,0,0});
            func->expression = ast.children[1]->expr();
        }
        return func;
    };
}


template<> void Ast::set_normalizer<Grammar::kwargs_only_func::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto func = std::make_unique<Function>(ast.source());
        func->args = std::make_unique<ListBinding>(Source {0,0,0});
        func->kwargs = ast.children[0]->binding();
        func->expression = ast.children[1]->expr();
        return func;
    };
}


template<> void Ast::set_normalizer<Grammar::postfix::funcall_operator>() {
    normalizer = [](const Ast& ast, ExprPtr expr) -> ExprPtr {
        auto call = std::make_unique<FunCall>(ast.source(), std::move(expr));
        for (auto& c : ast.children)
            call->elements.push_back(c->collection_element());
        return call;
    };
}


template<> void Ast::set_normalizer<Grammar::postfix::object_access>() {
    normalizer = [](const Ast& ast, ExprPtr expr) -> ExprPtr {
        auto name = Object::string(ast.children[0]->string());
        auto index = std::make_unique<Literal>(ast.children[0]->source(), name);
        return std::make_unique<Index>(ast.source(), std::move(expr), std::move(index));
    };
}


template<> void Ast::set_normalizer<Grammar::postfix::subscript_operator>() {
    normalizer = [](const Ast& ast, ExprPtr expr) -> ExprPtr {
        auto index = ast.children[0]->expr();
        return std::make_unique<Index>(ast.source(), std::move(expr), std::move(index));
    };
}


template<> void Ast::set_normalizer<Grammar::postfix::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto expr = ast.children[0]->expr();
        for (auto it = ast.children.begin() + 1; it != ast.children.end(); it++)
            expr = (*it)->postfix(std::move(expr));
        return expr;
    };
}


template<> void Ast::set_normalizer<Grammar::prefix::rule>() {
    normalizer = [](const Ast& ast) -> ExprPtr {
        auto it = ast.children.rbegin();
        auto expr = (*it++)->expr();
        while (it != ast.children.rend()) {
            auto op = (*it)->unop();
            auto src = (*it++)->source();
            expr = std::make_unique<UnOp>(src, std::move(expr), op);
        }
        return expr;
    };
}


static ExprPtr _lbinop(const Ast& ast) {
    auto expr = ast.children[0]->expr();
    for (auto it = ast.children.begin() + 1; it != ast.children.end(); it++) {
        auto src = (*it)->source();
        auto op = (*it++)->binop();
        auto rhs =  (*it)->expr();
        expr = std::make_unique<BinOp>(src, std::move(expr), std::move(rhs), op);
    }
    return expr;
}

static ExprPtr _rbinop(const Ast& ast) {
    auto lhs = ast.children[0]->expr();
    if (ast.children.size() == 1)
        return lhs;
    return std::make_unique<BinOp>(
        ast.children[1]->source(),
        std::move(lhs),
        ast.children[2]->expr(),
        ast.children[1]->binop()
    );
}

template<> void Ast::set_normalizer<Grammar::power>() { normalizer = _rbinop; }
template<> void Ast::set_normalizer<Grammar::product>() { normalizer = _lbinop; }
template<> void Ast::set_normalizer<Grammar::sum>() { normalizer = _lbinop; }
template<> void Ast::set_normalizer<Grammar::ineq>() { normalizer = _lbinop; }
template<> void Ast::set_normalizer<Grammar::eq>() { normalizer = _lbinop; }
template<> void Ast::set_normalizer<Grammar::conj>() { normalizer = _lbinop; }
template<> void Ast::set_normalizer<Grammar::disj>() { normalizer = _lbinop; }

template<> void Ast::set_normalizer<Grammar::keyword::And>() { normalizer = BinaryOperator::conjunction; }
template<> void Ast::set_normalizer<Grammar::keyword::Or>() { normalizer = BinaryOperator::disjunction; }
template<> void Ast::set_normalizer<Grammar::op::power>() { normalizer = BinaryOperator::power; }
template<> void Ast::set_normalizer<Grammar::op::divide>() { normalizer = BinaryOperator::divide; }
template<> void Ast::set_normalizer<Grammar::op::idivide>() { normalizer = BinaryOperator::integer_divide; }
template<> void Ast::set_normalizer<Grammar::op::multiply>() { normalizer = BinaryOperator::multiply; }
template<> void Ast::set_normalizer<Grammar::op::plus>() { normalizer = BinaryOperator::plus; }
template<> void Ast::set_normalizer<Grammar::op::minus>() { normalizer = BinaryOperator::minus; }
template<> void Ast::set_normalizer<Grammar::op::le>() { normalizer = BinaryOperator::less_than_or_eq; }
template<> void Ast::set_normalizer<Grammar::op::ge>() { normalizer = BinaryOperator::greater_than_or_eq; }
template<> void Ast::set_normalizer<Grammar::op::lt>() { normalizer = BinaryOperator::less_than; }
template<> void Ast::set_normalizer<Grammar::op::gt>() { normalizer = BinaryOperator::greater_than; }
template<> void Ast::set_normalizer<Grammar::op::dbleq>() { normalizer = BinaryOperator::equal; }
template<> void Ast::set_normalizer<Grammar::op::ineq>() { normalizer = BinaryOperator::not_equal; }

template<> void Ast::set_normalizer<Grammar::op::un_minus>() { normalizer = UnaryOperator::negate; }
