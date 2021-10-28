//
// Created by james on 9/14/2021.
//

#ifndef FACTSAUTOMATON_H
#define FACTSAUTOMATON_H
#include "Automaton.h"

class FactsAutomaton : public Automaton {
private:
    void Sa(const std::string& input);
    void Sc(const std::string& input);
    void St(const std::string& input);
    void Ss(const std::string& input);

public:
    FactsAutomaton() : Automaton(TokenType::FACTS){}

    void S0(const std::string& input);

};


#endif //PROJECT1_FACTSAUTOMATON_H
