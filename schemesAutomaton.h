//
// Created by james on 9/14/2021.
//

#ifndef SCHEMESAUTOMATON_H
#define SCHEMESAUTOMATON_H
#include "Automaton.h"


class schemesAutomaton : public Automaton {
private:
    void Sc(const std::string& input);
    void Sh(const std::string& input);
    void Se1(const std::string& input);
    void Sm(const std::string& input);
    void Se2(const std::string& input);
    void Ss(const std::string& input);

public:
    schemesAutomaton() : Automaton(TokenType::SCHEMES){}
    void S0(const std::string& input);
};


#endif //PROJECT1_SCHEMESAUTOMATON_H
