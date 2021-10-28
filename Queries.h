//
// Created by james on 9/14/2021.
//

#ifndef QUERIES_H
#define QUERIES_H
#include "Automaton.h"

class Queries : public Automaton
{
private:
    void Su(const std::string& input);
    void Se(const std::string& input);
    void Sr(const std::string& input);
    void Si(const std::string& input);
    void Se2(const std::string& input);
    void Ss(const std::string& input);

public:
    Queries() : Automaton(TokenType::QUERIES) {}  // Call the base constructor

    void S0(const std::string& input);

};


#endif //PROJECT1_QUERIES_H
