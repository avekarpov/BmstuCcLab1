#include <iostream>
#include <iomanip>
#include <string>
#include <list>
#include <vector>
#include <cassert>
#include <queue>
#include <set>
#include <map>
#include <format>

using State = size_t;

using Term = char;
static constexpr Term Eps { '\0' };

template <bool is_multi>
using StateTranslations = std::map<Term, std::conditional_t<is_multi, std::set<State>, State>>;

template <bool is_multi>
using FsmTranslations = std::vector<StateTranslations<is_multi>>;

template <bool is_multi>
class FsmBase
{
public:
    FsmBase() = default;

    FsmBase(std::set<Term> terms, FsmTranslations<is_multi> translations)
    : _terms { std::move(terms) }
    , _translations { std::move(translations) }
    {}

    const std::set<Term> &terms() const
    {
        return _terms;
    }

    const FsmTranslations<is_multi> &translations() const
    {
        return _translations;
    }

    bool empty() const
    {
        return _terms.empty();
    }

    const StateTranslations<is_multi> &at(const State index) const
    {
        if (size() <= index)
        {
            throw std::runtime_error { "out of state" };
        }

        return _translations[index];
    }

    size_t size() const
    {
        return _translations.size();
    }

protected:
    std::set<Term> _terms;
    FsmTranslations<is_multi> _translations;
};

class Fsm : public FsmBase<true>
{
public:
    Fsm ()
    {
        _translations.emplace_back();
    }
    
    Fsm (Term term)
    {
        _terms.emplace(term);
        _translations.emplace_back();
        _translations.emplace_back();
        _translations.front()[term].insert(endState());
    }

    State endState() const
    {
        return _translations.size() - 1;
    }

    Fsm operator|(const Fsm &other) const
    {
        if (empty())
        {
            return other;
        }

        if (other.empty())
        {
            return *this;
        }
        
        Fsm fsm = *this;

        fsm._terms.insert(other._terms.begin(), other._terms.end());

        const auto shift_other_state = fsm.size();
        for (State state = 0; state < other.size(); ++state)
        {
            fsm._translations.emplace_back(other.at(state));
            for (auto &[_, new_states] : fsm._translations.back())
            {
                std::set<State> states;
                for (auto &new_state : new_states)
                {
                    states.insert(new_state + shift_other_state);
                }
                new_states = states;
            }
        }

        fsm[0][Eps].insert(endState() + 1); // Go to 2nd fsm
        fsm[endState()][Eps].insert(fsm.endState()); // Go to exit from 1st fsm

        return fsm;
    }

    Fsm &operator|=(const Fsm &other)
    {
        *this = *this | other;

        return *this;
    }

    Fsm operator&(const Fsm &other) const
    {
        if (empty())
        {
            return other;
        }

        if (other.empty())
        {
            return *this;
        }

        Fsm fsm = *this;

        fsm._terms.insert(other._terms.begin(), other._terms.end());

        const auto shift_other_state = fsm.size();
        for (size_t state = 0; state < other.size(); ++state)
        {
            fsm._translations.emplace_back(other.at(state));
            for (auto &[_, new_states] : fsm._translations.back())
            {
                std::set<State> states;
                for (auto &new_state : new_states)
                {
                    states.insert(new_state + shift_other_state);
                }
                new_states = states;
            }
        }

        fsm[endState()][Eps].insert(endState() + 1); // Go to 2nd after 1st fsm

        return fsm;
    }

    Fsm &operator&=(const Fsm &other)
    {
        *this = *this & other;

        return *this;
    }

    Fsm &addBrackets()
    {
        shiftLeft(1);
        _translations[0][Eps].insert(1);
        shiftRight(1);
        _translations[endState() - 1][Eps].insert(endState());

        return *this;
    }

    Fsm &addRepeat()
    {
        shiftRight(1);
        _translations[endState() - 1][Eps].insert(0);
        _translations[endState() - 1][Eps].insert(endState());
        shiftLeft(1);
        _translations[0][Eps].insert(1);
        _translations[0][Eps].insert(endState());

        return *this;
    }

    Fsm &addOptional()
    {
        shiftRight(1);
        _translations[endState() - 1][Eps].insert(endState());
        shiftLeft(1);
        _translations[0][Eps].insert(1);
        _translations[0][Eps].insert(endState());

        return *this;
    }

    friend std::ostream &operator<<(std::ostream& os, const Fsm &fsm)
    {
        for (size_t i = 0; i < fsm.size(); ++i)
        {
            os << i << ": [";
            for (const auto &[key, new_states] : fsm.at(i))
            {
                if (key == Eps)
                {
                    os << "ε";
                }
                else
                {
                    os << key;
                }
                os << ": ";
                for (const auto new_state : new_states)
                {
                    os << new_state << ", ";
                }
            }
            os << "]\n";
        }
        os << "end state: " << fsm.endState();

        return os;
    }

    std::string toGraphviz() const
    {
        const auto translations = [this]()
        {
            std::string result;

            for (State state = 0; state < size(); ++state)
            {
                for (const auto &[key, new_states] : _translations[state])
                {
                    for (const auto new_state : new_states)
                    {
                        std::format_to(
                            std::back_inserter(result), 
                            R"({} -> {} [label = "{}"];)", 
                            state, 
                            new_state, 
                            (key == Eps ? "ε" : std::string { key })
                        );
                    }
                }
            }

            return result;
        };

        return std::format(
            R"(
                digraph G {{
                    rankdir = "LR"
                    {{
                        {} [shape=doublecircle]
                    }}
                    {}
                }}
            )",
            endState(),
            translations()
        );
    }

private:
    StateTranslations<true> &operator[](const size_t index)
    {
        return _translations[index];
    }

    void shiftLeft(const size_t index = 1)
    {
        for (size_t i = 0; i < index; ++i)
        {
            _translations.emplace_back();
        }
        for (auto i = size() - 1; index <= i; --i)
        {
            _translations[i] = std::move(_translations[i - index]);
            for (auto &[_, new_states] : _translations[i])
            {
                std::set<State> states;
                for (auto &new_state : new_states)
                {
                    states.insert(new_state + index);
                }
                new_states = states;
            }
        }
    }

    void shiftRight(const size_t index = 1)
    {
        for (size_t i = 0; i < index; ++i)
        {
            _translations.emplace_back();
        }
    }
};

class DFsm : public FsmBase<false>
{
public:
    DFsm(std::set<Term> terms, FsmTranslations<false> translations, std::set<State> end_states)
    : FsmBase<false> { std::move(terms), std::move(translations) }
    , _end_states { std::move(end_states) }
    {}

    const std::set<State>& endStates() const
    {
        return _end_states;
    }

    bool isEndState(const State state) const
    {
        return _end_states.find(state) != _end_states.end();
    }

    friend std::ostream &operator<<(std::ostream& os, const DFsm &dfsm)
    {
        for (size_t i = 0; i < dfsm.size(); ++i)
        {
            os << i << ": [";
            for (const auto &[key, new_state] : dfsm.at(i))
            {
                os << key << ": " << new_state << ", ";
            }
            os << "]\n";
        }
        os << "end states: ";
        for (const auto end_state : dfsm.endStates())
        {
            os << end_state << ", ";
        }

        return os;
    }

    std::string toGraphviz() const
    {
        const auto endStates = [this]()
        {
            std::string result;

            for (const auto &end_state : _end_states)
            {
                std::format_to(
                    std::back_inserter(result),
                    R"({} [shape=doublecircle];)",
                    end_state
                );
            };

            return result;
        };

        const auto translations = [this]()
        {
            std::string result;

            for (State state = 0; state < size(); ++state)
            {
                for (const auto &[key, new_state] : _translations[state])
                {
                    std::format_to(
                        std::back_inserter(result), 
                        R"({} -> {} [label = "{}"];)", 
                        state, 
                        new_state, 
                        (key == Eps ? "ε" : std::string { key })
                    );
                }
            }

            return result;
        };

        return std::format(
            R"(
                digraph G {{
                    rankdir = "LR"
                    {{
                        {}
                    }}
                    {}
                }}
            )",
            endStates(),
            translations()
        );
    }

private:
    std::set<State> _end_states;
};

class RegexParser
{
private:
    class Lexer
    {
    public:
        Lexer(std::string string)
        : _index { 0 }
        , _string { std::move(string) }
        {}

        char peek() const
        {
            if (isEnd())
            {
                throw std::runtime_error { "Call peek on end of string" };
            }

            return _string[_index];
        }

        void pop()
        {
            if (isEnd())
            {
                throw std::runtime_error { "Call pop on end of string" };
            }

            ++_index;
        }

        bool isEnd() const
        {
            return _index == _string.size();
        }

    private:
        size_t _index;

        const std::string _string;
    };

    struct AstNode
    {
        using Ptr = std::shared_ptr<AstNode>;

        AstNode(Term term, Ptr l, Ptr r)
        : term { term }
        , left { l }
        , right { r }
        {}

        Term term;
        Ptr left;
        Ptr right;
    };
    using AstNodePtr = AstNode::Ptr;

    class Ast
    {
    public:
        Ast(const std::string &string)
        {
            Lexer lexer { prepare(string) };

            _root = parseSubregex(lexer);
        }

        const AstNodePtr root() const
        {
            return _root;
        }

    private:
        static std::string prepare(const std::string string)
        {
            std::string result;
            result.reserve(string.size() * 2);

            for (size_t i = 0; i < string.size() - 1; ++i)
            {
                const auto c = string[i];
                const auto n = string[i + 1];

                result.push_back(c);
                if (
                    (std::isalnum(c) || c == ')' || c == '*' || c == '?') &&
                    (n != ')' && n != '|' && n != '*' && n != '?')
                )
                {
                    result.push_back('&');
                }
            }
            {
                result.push_back(string.back());
            }

            return result;
        }

        AstNodePtr parseSubregex(Lexer &lexer)
        {
            AstNodePtr left = parseConcatination(lexer);

            if (not lexer.isEnd() && lexer.peek() == '|')
            {
                lexer.pop();

                return std::make_shared<AstNode>('|', left, parseSubregex(lexer));
            }
            else
            {
                return left;
            }
        }

        AstNodePtr parseConcatination(Lexer &lexer)
        {
            AstNodePtr left = parseRepeat(lexer);

            if (not lexer.isEnd() && lexer.peek() == '&')
            {
                lexer.pop();

                return std::make_shared<AstNode>('&', left, parseConcatination(lexer));
            }
            else
            {
                return left;
            }
        }

        AstNodePtr parseRepeat(Lexer &lexer)
        {
            AstNodePtr left = parseAtom(lexer);

            if (not lexer.isEnd() && lexer.peek() == '*')
            {
                lexer.pop();

                return std::make_shared<AstNode>('*', left, nullptr);
            }
            else if (not lexer.isEnd() && lexer.peek() == '?')
            {
                lexer.pop();

                return std::make_shared<AstNode>('?', left, nullptr);
            }
            else
            {
                return left;
            }
        }

        AstNodePtr parseAtom(Lexer &lexer)
        {
            AstNodePtr node;

            if (not lexer.isEnd() && lexer.peek() == '(')
            {
                lexer.pop();

                node = parseSubregex(lexer);

                const auto c = lexer.peek();
                
                if (c != ')')
                {
                    throw std::invalid_argument { std::format(R"(got {}, expect ')')", c) };
                }

                lexer.pop();
            }
            else if (not lexer.isEnd())
            {
                const auto c = lexer.peek();

                if (not std::isalnum(c))
                {
                    throw std::invalid_argument { std::format(R"(got {}, expect char or digit)", c) };
                }

                lexer.pop();

                node = std::make_shared<AstNode>(c, nullptr, nullptr);
            }

            return node;
        }

    private:
        AstNodePtr _root;
    };

public:
    Fsm parseToFsm(const std::string& string) const
    {
        Ast ast { string };
        
        return parseAstNode(ast.root());
    }

private:
    Fsm parseAstNode(const AstNodePtr node) const
    {
        switch (node->term)
        {
            case '|':
            {
                return parseAstNode(node->left) | parseAstNode(node->right);
            }

            case '&':
            {
                return parseAstNode(node->left) & parseAstNode(node->right);
            }

            case '*':
            {
                return parseAstNode(node->left).addRepeat();
            }

            case '?':
            {
                return parseAstNode(node->left).addOptional();
            }

            default:
            {
                return Fsm { node->term };
            }
        }
    }

};

class FsmDeterminizer
{
public:
    DFsm determine(const Fsm &fsm)
    {
        std::map<std::set<State>, State> mapping;
        FsmTranslations<false> translations;
        std::set<std::set<State>> queue;

        std::set<State> start_state;
        addEpsClosure(fsm, start_state, 0);

        mapping[start_state] = translations.size();
        translations.emplace_back();
        queue.insert(start_state);

        while (not queue.empty())
        {
            const auto state = std::move(*queue.begin());
            queue.erase(queue.begin());

            for (const auto term : fsm.terms())
            {
                const auto new_state = epsClosure(fsm, move(fsm, state, term));

                if (new_state.empty())
                {
                    continue;
                }
                
                if (mapping.find(new_state) == mapping.end())
                {
                    mapping[new_state] = translations.size();
                    translations.emplace_back();
                    queue.insert(new_state);
                }

                translations[mapping[state]][term] = mapping[new_state];
            }
        }

        std::set<State> end_states;
        for (const auto &[fsm_states, dfsm_state] : mapping)
        {
            if (fsm_states.count(fsm.endState()) != 0)
            {
                end_states.insert(dfsm_state);
            }
        }

        return DFsm { fsm.terms(), std::move(translations), std::move(end_states) };
    }

private:
    void addEpsClosure(const Fsm &fsm, std::set<State> &closure, const State input_state)
    {
        closure.insert(input_state);

        if (input_state != fsm.endState())
        {
            for (const auto &[key, new_states] : fsm.at(input_state))
            {
                if (key == Eps)
                {
                    for (const auto new_state : new_states)
                    {
                        if (closure.count(new_state) == 0)
                        {
                            addEpsClosure(fsm, closure, new_state);
                        }
                    }
                }
            }
        }
    }

    std::set<State> epsClosure(const Fsm &fsm, const std::set<State> &input_states)
    {
        std::set<State> clouser { input_states.begin(), input_states.end() };

        for (const auto state : input_states)
        {
            addEpsClosure(fsm, clouser, state);
        }

        return clouser;
    }

    std::set<State> move(const Fsm &fsm, const std::set<State> &input_states, const Term term)
    {
        std::set<State> result;

        for (auto state : input_states)
        {
            if (state == fsm.endState())
            {
                continue;
            }

            for (const auto &[key, new_states] : fsm.at(state))
            {
                if (key == term)
                {
                    result.insert(new_states.begin(), new_states.end());
                }
            }
        }

        return result;
    }
};

class DFsmMinimizer
{
public:
    DFsm minimize(const DFsm &dfsm)
    {
        std::set<State> reachable_states;
        addReachableStates(dfsm, reachable_states);

        FsmTranslations<true> reverse_translations;
        reverse_translations.resize(dfsm.size() + 1);
        for (State state = 0; state < dfsm.size(); ++state)
        {
            for (const auto [key, new_state] : dfsm.at(state))
            {
                reverse_translations[new_state][key].insert(state);
            }
        }
        for (State state = 0; state < dfsm.size(); ++state)
        {
            for (const auto key : dfsm.terms())
            {
                const auto &state_translations = dfsm.at(state);
                if (state_translations.find(key) == state_translations.end())
                {
                    reverse_translations.back()[key].insert(state);
                }
            }
        }
        for (const auto key : dfsm.terms())
        {
            reverse_translations.back()[key].insert(dfsm.size());
        }

        std::vector<std::vector<bool>> marked;
        marked.resize(dfsm.size() + 1);
        for (State i = 0; i < marked.size(); ++i)
        {
            marked[i].resize(dfsm.size() + 1);   
        }
        std::list<std::pair<State, State>> queue;
        for (State i = 0; i < marked.size() - 1; ++i)
        {
            marked[i][i] = false;

            for (State j = i + 1; j < marked[i].size() - 1; ++j)
            {
                if (dfsm.isEndState(i) != dfsm.isEndState(j))
                {
                    marked[j][i] = marked[i][j] = true;
                    queue.emplace_back(i, j);
                }
            }
        }
        for (State state = 0; state < dfsm.size(); ++state)
        {
            if (dfsm.isEndState(state))
            {
                marked[state][dfsm.size()] = marked[dfsm.size()][state] =  true;
                queue.emplace_back(state, dfsm.size());
            }
        }
        marked[dfsm.size()][dfsm.size()] = false;

        while (not queue.empty())
        {
            const auto [l_state, r_state] = queue.front();

            for (const auto term : dfsm.terms())
            {
                for (const auto l_prev_state : reverse_translations[l_state][term])
                {
                    for (const auto r_prev_state : reverse_translations[r_state][term])
                    {
                        if (not marked[l_prev_state][r_prev_state])
                        {
                            marked[r_prev_state][l_prev_state] = marked[l_prev_state][r_prev_state] = true;
                            queue.emplace_back(l_prev_state, r_prev_state);
                        }
                    }
                }
            }

            queue.pop_front();
        }

        for (State state = 0; state < dfsm.size(); ++state)
        {
            marked[state].pop_back();
        }
        marked.pop_back();

        std::vector<std::optional<State>> equal_states;
        equal_states.resize(dfsm.size(), std::nullopt);
        for (State i = 0; i < dfsm.size(); ++i)
        {
            for (State j = i + 1; j < dfsm.size(); ++j)
            {
                if (not marked[i][j])
                {
                    equal_states[j] = i;
                }
            }
        }

        std::map<State, State> mapping;
        FsmTranslations<false> translations;
        for (State state = 0; state < equal_states.size(); ++state)
        {
            if (not equal_states[state].has_value())
            {
                mapping[state] = translations.size();
                translations.emplace_back();
            }
        }

        std::set<State> end_states;
        for (State state = 0; state < dfsm.size(); ++state)
        {
            if (reachable_states.count(state) == 0)
            {
                continue;
            }

            if (not equal_states[state].has_value() && dfsm.isEndState(state))
            {
                end_states.insert(mapping[state]);
            }

            for (const auto &[key, new_state] : dfsm.at(state))
            {
                translations[
                    mapping[equal_states[state].has_value() ? equal_states[state].value() : state]
                ][key] = 
                    mapping[equal_states[new_state].has_value() ? equal_states[new_state].value() : new_state];
            }
        }

        return DFsm { dfsm.terms(), std::move(translations), std::move(end_states) };
    }

private:
    void addReachableStates(const DFsm &dfsm, std::set<State> &reachable_states, const State from_state = 0)
    {
        reachable_states.insert(from_state);

        if (from_state < dfsm.size())
        {
            const auto &translations = dfsm.at(from_state);
            for (const auto &[_, new_state] : translations)
            {
                if (reachable_states.count(new_state) == 0)
                {
                    addReachableStates(dfsm, reachable_states, new_state);
                }
            }
        }
    }
};

template <class T>
void graphviz(const T &fsm, std::string name)
{
    std::system(std::format(R"(echo '{}' | dot -Tsvg > {}.svg && open -a "Google Chrome" ./{}.svg)", fsm.toGraphviz(), name, name).data());
}

int main(int argc, char *argv[])
{
    std::string input;
    std::cin >> input;

    RegexParser parser;
    const auto nfsm = parser.parseToFsm(input);
    std::cout << nfsm << std::endl;
    graphviz(nfsm, "nfsm");

    FsmDeterminizer determinizer;
    const auto dfsm = determinizer.determine(nfsm);
    std::cout << dfsm << std::endl;
    graphviz(dfsm, "dfsm");

    DFsmMinimizer minimizer;
    const auto mdfsm = minimizer.minimize(dfsm);
    std::cout << mdfsm << std::endl;
    graphviz(mdfsm, "mdfsm");

    return EXIT_SUCCESS;
}

