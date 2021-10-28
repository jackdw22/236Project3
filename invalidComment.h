//
// Created by james on 9/15/2021.
//

#ifndef INVALIDCOMMENT_H
#define INVALIDCOMMENT_H
#include "Automaton.h"

class invalidComment: public Automaton {
private:
    void S1(const std::string& input);
    void S2(const std::string& input);
public:
    invalidComment() : Automaton(TokenType::UNDEFINED){}

    void S0(const std::string& input);

};


#endif //PROJECT1_INVALIDCOMMENT_H
