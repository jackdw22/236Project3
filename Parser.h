//
// Created by james on 9/28/2021


//
// Created by james on 9/28/2021.
//

#ifndef PARSER_H
#define PARSER_H

#include "Token.h"
#include "Lexer.h"
#include "Predicate.h"
#include "Rule.h"
#include "Parameter.h"
#include <vector>
#include <iostream>
#include <string>
#include "DatalogProgram.h"


class Parser {

public:
    DatalogProgram* Datalog;
    Parser();
    void Parse(std::vector<Token*> tokens);
private:

};


#endif //PARSER_H

