//
// Created by james on 9/14/2021.
//

#ifndef MULTIPLYAUTOMATON_H
#define MULTIPLYAUTOMATON_H
#include "Automaton.h"


class MultiplyAutomaton : public Automaton
        {
        public:
            MultiplyAutomaton() : Automaton(TokenType::MULTIPLY){}

            void S0(const std::string& input);

};


#endif //MULTIPLYAUTOMATON_H
