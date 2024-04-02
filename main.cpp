#include <iostream>
#include <string>
#include <list>
#include <vector>
#include <cassert>

class Fsm
{
public:
    Fsm () = default;
    
    Fsm (char term)
    {
        _translations.emplace_back();
        _translations.back().emplace_back(std::string { term }, size());
    }

    const std::list<std::pair<std::string, size_t>> &operator[](const size_t index) const
    {
        return _translations[index];
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

        for (size_t state = 0; state < _translations.size(); ++state)
        {
            fsm._translations.emplace_back(_translations[state]);
        }
        fsm._translations.emplace_back(); // For exit from this fsm

        const auto shift_other_state = fsm._translations.size();
        for (size_t state = 0; state < other._translations.size(); ++state)
        {
            fsm._translations.emplace_back(other[state]);
            for (auto &[_, new_state] : fsm._translations.back())
            {
                new_state += shift_other_state;
            }
        }

        fsm[0].emplace_back("eps", size() + 1); // Go to 2nd fsm
        fsm[size()].emplace_back("eps", fsm.size()); // Go to exit from 1st fsm

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

        for (size_t state = 0; state < _translations.size(); ++state)
        {
            fsm._translations.emplace_back(_translations[state]);
        }
        fsm._translations.emplace_back(); // For connect to other fsm

        const auto shift_other_state = fsm._translations.size();
        for (size_t state = 0; state < other._translations.size(); ++state)
        {
            fsm._translations.emplace_back(other[state]);
            for (auto &[_, new_state] : fsm._translations.back())
            {
                new_state += shift_other_state;
            }
        }

        fsm[size()].emplace_back("eps", size() + 1); // Go to 2nd after 1st fsm

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
        _translations[0].emplace_back("eps", 1);
        shiftRight(1);
        _translations[size() - 1].emplace_back("eps", size());

        return *this;
    }

    Fsm &addRepeat()
    {
        _translations.emplace_back();
        _translations.back().emplace_back("eps", 0);
        _translations.back().emplace_back("eps", _translations.size());

        _translations.emplace_back();
        for (size_t i = _translations.size() - 1; 0 < i; --i)
        {
            _translations[i] = std::move(_translations[i - 1]);
            for (auto &[_, new_state] : _translations[i])
            {
                new_state += 1;
            }
        }
    
        _translations.front().emplace_back("eps", 1);
        _translations.front().emplace_back("eps", _translations.size());

        return *this;
    }

    Fsm &addOptional()
    {
        _translations.emplace_back();
        _translations.back().emplace_back("eps", _translations.size());

        _translations.emplace_back();
        for (size_t i = _translations.size() - 1; 0 < i; --i)
        {
            _translations[i] = std::move(_translations[i - 1]);
            for (auto &[_, new_state] : _translations[i])
            {
                new_state += 1;
            }
        }
    
        _translations.front().emplace_back("eps", 1);
        _translations.front().emplace_back("eps", _translations.size());

        return *this;
    }

    friend std::ostream &operator<<(std::ostream& os, const Fsm &fsm)
    {
        for (size_t i = 0; i < fsm.size(); ++i)
        {
            os << i << ": [";
            for (const auto &[key, new_state] : fsm._translations[i])
            {
                os << key << ": " << new_state << ", ";
            }
            os << "]\n";
        }

        return os;
    }

private:
    std::list<std::pair<std::string, size_t>> &operator[](const size_t index)
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
    std::vector<std::list<std::pair<std::string, size_t>>> _translations;
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
                    fsm &= parseSubregex(lexer).addBrackets();

                    assert(lexer.get() == ')');
                    lexer.next();

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
                    fsm &= parseSubregex(lexer);

                    break;
                }

                case '?':
                {
                    fsm.addOptional();
                    fsm &= parseSubregex(lexer);

                    break;
                }

                default:
                {
                    fsm &= Fsm { term };

                    break;
                }
            }

            // std::cout << "after " << term << "\n" << fsm << std::endl;
        }

        return fsm;
    }

};

int main(int argc, char *argv[])
{
    std::string input = "a?(b|c)*k";
    // std::cin >> input;

    RegexParser parser;
    std::cout << parser.parseToFsm(input) << std::endl;

    return EXIT_SUCCESS;
}

