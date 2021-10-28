//
// Created by james on 9/15/2021.
//

#ifndef INVALIDSTRINGAUTOMATON_H
#define INVALIDSTRINGAUTOMATON_H
#include "Automaton.h"


class InvalidStringAutomaton : public Automaton{
private:
    void S1(const std::string& input);
public:
    InvalidStringAutomaton() : Automaton(TokenType::UNDEFINED){}

    void S0(const std::string& input);

};


#endif //PROJECT1_INVALIDSTRINGAUTOMATON_H
