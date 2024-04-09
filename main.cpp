#include <iostream>
#include <iomanip>
#include <string>
#include <list>
#include <vector>
#include <cassert>

using State = size_t;
using StateTranslations = std::list<std::pair<std::string, size_t>>;
using FsmTranslations = std::vector<StateTranslations>;
static const std::string Eps { "eps" };

class Fsm
{
public:
    Fsm () = default;
    
    Fsm (char term)
    {
        _translations.emplace_back();
        _translations.back().emplace_back(std::string { term }, endState());
    }

    const StateTranslations &operator[](const State index) const
    {
        return _translations[index];
    }

    State endState() const
    {
        return _translations.size();
    }

    size_t size() const
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

        for (size_t state = 0; state < size(); ++state)
        {
            fsm._translations.emplace_back(_translations[state]);
        }
        fsm._translations.emplace_back(); // For exit from this fsm

        const auto shift_other_state = fsm.size();
        for (size_t state = 0; state < other.size(); ++state)
        {
            fsm._translations.emplace_back(other[state]);
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

        for (size_t state = 0; state < size(); ++state)
        {
            fsm._translations.emplace_back(_translations[state]);
        }
        fsm._translations.emplace_back(); // For connect to other fsm

        const auto shift_other_state = fsm.size();
        for (size_t state = 0; state < other.size(); ++state)
        {
            fsm._translations.emplace_back(other[state]);
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
            for (const auto &[key, new_state] : fsm[i])
            {
                os << key << ": " << new_state << ", ";
            }
            os << "]\n";
        }

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

private:
    FsmTranslations _translations;
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
    Fsm parseToFsm(std::string string)
    {
        Lexer lexer { std::move(string) };

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

int main(int argc, char *argv[])
{
    std::string input = "(a|b)*abb";
    // std::string input = "z*|(qw)?";
    // std::string input = "z*";
    // std::string input = "ab*cz*";
    // std::string input = "z(q)*";
    // std::string input = "(q)*";
    // std::string input = "a|(b)?";
    // std::cin >> input;

    RegexParser parser;
    std::cout << parser.parseToFsm(input) << std::endl;

    return EXIT_SUCCESS;
}

