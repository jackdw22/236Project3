//
// Created by james on 9/14/2021.
//

#ifndef RULESAUTOMATON_H
#define RULESAUTOMATON_H
#include "Automaton.h"

class RulesAutomaton : public Automaton{
private:
    void Su(const std::string& input);
    void Sl(const std::string& input);
    void Se(const std::string& input);
    void Ss(const std::string& input);
public:
    RulesAutomaton() : Automaton(TokenType::RULES){}

    void S0(const std::string& input);
};


#endif //PROJECT1_RULESAUTOMATON_H
