//
// Created by james on 9/14/2021.
//

#ifndef LEFTPARENAUTOMATON_H
#define LEFTPARENAUTOMATON_H
#include "Automaton.h"

class LeftParenAutomaton : public Automaton
        {
public:
    LeftParenAutomaton() : Automaton(TokenType::LEFT_PAREN) {}

    void S0(const std::string& input);

};


#endif //LEFTPARENAUTOMATON_H
