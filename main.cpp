#include <iostream>
#include <iomanip>
#include <string>
#include <list>
#include <vector>
#include <cassert>
#include <queue>
#include <set>
#include <map>

using State = size_t;

using Term = char;
static constexpr Term Eps { '\0' };

using StateTranslations = std::list<std::pair<Term, size_t>>;
using FsmTranslations = std::vector<StateTranslations>;

class FsmBase
{
public:
    FsmBase() = default;

    FsmBase(std::set<Term> terms, FsmTranslations transactions)
    : _terms { std::move(terms) }
    , _translations { std::move(transactions) }
    {}

    const std::set<Term> &terms() const
    {
        return _terms;
    }

    const StateTranslations &at(const State index) const
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
    FsmTranslations _translations;
};

class Fsm : public FsmBase
{
public:
    Fsm () = default;
    
    Fsm (Term term)
    {
        _terms.emplace(term);
        _translations.emplace_back();
        _translations.back().emplace_back(term, endState());
    }

    const StateTranslations &at(const State index) const
    {
        if (endState() == index)
        {
            throw std::runtime_error { "access meta end state"};
        }

        return FsmBase::at(index);
    }

    State endState() const
    {
        return _translations.size();
    }

    bool empty() const
    {
        return _translations.empty();
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
        
        Fsm fsm;

        fsm._terms.insert(_terms.begin(), _terms.end());
        fsm._terms.insert(other._terms.begin(), other._terms.end());

        for (size_t state = 0; state < size(); ++state)
        {
            fsm._translations.emplace_back(_translations[state]);
        }
        fsm._translations.emplace_back(); // For exit from this fsm

        const auto shift_other_state = fsm.size();
        for (size_t state = 0; state < other.size(); ++state)
        {
            fsm._translations.emplace_back(other.at(state));
            for (auto &[_, new_state] : fsm._translations.back())
            {
                new_state += shift_other_state;
            }
        }

        fsm[0].emplace_back(Eps, endState() + 1); // Go to 2nd fsm
        fsm[endState()].emplace_back(Eps, fsm.endState()); // Go to exit from 1st fsm

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

        Fsm fsm;

        fsm._terms.insert(_terms.begin(), _terms.end());
        fsm._terms.insert(other._terms.begin(), other._terms.end());

        for (size_t state = 0; state < size(); ++state)
        {
            fsm._translations.emplace_back(_translations[state]);
        }
        fsm._translations.emplace_back(); // For connect to other fsm

        const auto shift_other_state = fsm.size();
        for (size_t state = 0; state < other.size(); ++state)
        {
            fsm._translations.emplace_back(other.at(state));
            for (auto &[_, new_state] : fsm._translations.back())
            {
                new_state += shift_other_state;
            }
        }

        fsm[endState()].emplace_back(Eps, endState() + 1); // Go to 2nd after 1st fsm

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
        _translations[0].emplace_back(Eps, 1);
        shiftRight(1);
        _translations[endState() - 1].emplace_back(Eps, endState());

        return *this;
    }

    Fsm &addRepeat()
    {
        shiftRight(1);
        _translations[endState() - 1].emplace_back(Eps, 0);
        _translations[endState() - 1].emplace_back(Eps, endState());
        shiftLeft(1);
        _translations[0].emplace_back(Eps, 1);
        _translations[0].emplace_back(Eps, endState());

        return *this;
    }

    Fsm &addOptional()
    {
        shiftRight(1);
        _translations[endState() - 1].emplace_back(Eps, endState());
        shiftLeft(1);
        _translations[0].emplace_back(Eps, 1);
        _translations[0].emplace_back(Eps, endState());

        return *this;
    }

    friend std::ostream &operator<<(std::ostream& os, const Fsm &fsm)
    {
        for (size_t i = 0; i < fsm.size(); ++i)
        {
            os << i << ": [";
            for (const auto &[key, new_state] : fsm.at(i))
            {
                if (key == Eps)
                {
                    os << "ε";
                }
                else
                {
                    os << key;
                }
                os << ": " << new_state << ", ";
            }
            os << "]\n";
        }
        os << "end state: " << fsm.endState();

        return os;
    }

private:
    StateTranslations &operator[](const size_t index)
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
            for (auto &[_, new_state] : _translations[i])
            {
                new_state += index;
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

class DFsm : public FsmBase
{
public:
    DFsm(std::set<Term> terms, FsmTranslations transactions, std::set<State> end_states)
    : FsmBase { std::move(terms), std::move(transactions) }
    , _end_states { std::move(end_states) }
    {}

    const std::set<State> endStates() const
    {
        return _end_states;
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

        char get() const
        {
            if (isEnd())
            {
                throw std::runtime_error { "Call get on end of string" };
            }

            return _string[_index];
        }

        void next()
        {
            if (isEnd())
            {
                throw std::runtime_error { "Call next on end of string" };
            }

            ++_index;
        }

        void rollback()
        {
            if (_index == 0)
            {
                throw std::runtime_error { "Call rollback on start of string" };
            }

            --_index;
        }

        bool isEnd() const
        {
            return _index == _string.size();
        }

    private:
        size_t _index;

        const std::string _string;
    };

public:
    Fsm parseToFsm(std::string regex)
    {
        Lexer lexer { std::move(regex) };

        return parseSubregex(lexer);
    }

private:
    Fsm parseSubregex(Lexer &lexer)
    {
        Fsm fsm;

        while (not lexer.isEnd())
        {
            const auto term = lexer.get();
            lexer.next();

            switch (term)
            {
                case '(':
                {
                    if (not fsm.empty())
                    {
                        lexer.rollback();
                        fsm &= parseSubregex(lexer);
                    }
                    else
                    {
                        fsm = parseSubregex(lexer).addBrackets();

                        assert(lexer.get() == ')');
                        lexer.next();
                    }

                    break;
                }

                case ')':
                {
                    lexer.rollback();

                    return fsm;
                }

                case '|':
                {
                    fsm |= parseSubregex(lexer);

                    break;
                }

                case '*':
                {
                    fsm.addRepeat();

                    break;
                }

                case '?':
                {
                    fsm.addOptional();

                    break;
                }

                default:
                {
                    if (not fsm.empty())
                    {
                        lexer.rollback();
                        fsm &= parseSubregex(lexer);
                    }
                    else
                    {
                        fsm = Fsm { term };
                    }

                    break;
                }
            }
        }

        return fsm;
    }

};

class FsmDeterminizer
{
public:
    DFsm determine(const Fsm &fsm)
    {
        std::map<std::set<State>, State> mapping;
        FsmTranslations transactions;
        std::set<std::set<State>> queue;

        const auto start_state = epsClosure(fsm, 0);

        mapping[start_state] = transactions.size();
        transactions.emplace_back();
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
                    mapping[new_state] = transactions.size();
                    transactions.emplace_back();
                    queue.insert(new_state);
                }

                transactions[mapping[state]].emplace_back(term, mapping[new_state]);
            }
        }

        std::set<State> end_states;
        for (const auto &[fsm_states, dfsm_state] : mapping)
        {
            if (fsm_states.find(fsm.endState()) != fsm_states.end())
            {
                end_states.insert(dfsm_state);
            }
        }

        return DFsm { fsm.terms(), std::move(transactions), std::move(end_states) };
    }

private:
    std::set<State> singleEpsClosure(const Fsm &fsm, const State input_state)
    {
        std::set<State> result;

        if (input_state != fsm.endState())
        {
            for (const auto &[key, new_state] : fsm.at(input_state))
            {
                if (key == Eps)
                {
                    result.emplace(new_state);
                }
            }
        }

        return result;
    }

    std::set<State> epsClosure(const Fsm &fsm, const std::set<State> &input_states)
    {
        std::set<State> result { input_states.begin(), input_states.end() };

        for (const auto state : input_states)
        {
            const auto result_size_before = result.size();

            auto new_states = singleEpsClosure(fsm, state);
            result.insert(new_states.begin(), new_states.end());
            
            if (result_size_before < result.size())
            {
                new_states = epsClosure(fsm, new_states);
                result.insert(new_states.begin(), new_states.end());
            }
        }

        return result;
    }

    std::set<State> epsClosure(const Fsm &fsm, const State input_state)
    {
        return epsClosure(fsm, std::set<State> { input_state });
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

            for (const auto &[key, new_state] : fsm.at(state))
            {
                if (key == term)
                {
                    result.insert(new_state);
                }
            }
        }

        return result;
    }
};

int main(int argc, char *argv[])
{
    // std::string input = "b|a*";
    std::string input = "(a|b)*abb";
    // std::string input = "z*|(qw)?";
    // std::string input = "ab*cz*";
    // std::string input = "z(q)*";
    // std::string input = "(q)*";
    // std::string input = "a|(b)?";
    // std::cin >> input;

    RegexParser parser;
    const auto nfsm = parser.parseToFsm(input);
    std::cout << nfsm << "\n" << std::endl;

    FsmDeterminizer determinizer;
    const auto dfsm = determinizer.determine(nfsm);
    std::cout << dfsm << "\n" << std::endl;

    return EXIT_SUCCESS;
}

