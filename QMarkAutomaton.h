//
// Created by james on 9/14/2021.
//

#ifndef QMARKAUTOMATON_H
#define QMARKAUTOMATON_H
#include "Automaton.h"

class QMarkAutomaton : public Automaton{
public:
    QMarkAutomaton() : Automaton(TokenType::Q_MARK){}

    void S0(const std::string& input);

};


#endif //QMARKAUTOMATON_H
