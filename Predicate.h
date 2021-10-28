//
// Created by james on 9/29/2021.
//

#ifndef PREDICATE_H
#define PREDICATE_H
#include "Parameter.h"
#include <vector>
#include <iostream>
#include <string>
#include "Token.h"
#include "Lexer.h"
#include <set>


class Predicate {

public:
    Predicate(std::string name, std::string type);
    void addParameter(Parameter*);
    void predicateParse(std::vector<Token*>& tokens);
    void LEFT_PAREN(std::vector<Token*>& tokens);
    void parameter(std::vector<Token*>& tokens);
    void RIGHT_PAREN(std::vector<Token*>& tokens);
    void ID(std::vector<Token*>& tokens);
    void COMMA(std::vector<Token*>& tokens);
    std::string getParameters();
    void getDomain();
    std::string namePredicate;
    std::set<std::string> domains;
    std::vector<Parameter*> parameters;
    std::string type;
};


#endif //PROJECT1_PREDICATE_H
