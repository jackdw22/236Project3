//
// Created by james on 10/26/2021.
//

#ifndef INTERPRETER_H
#define INTERPRETER_H
#include "Parser.h"
#include "DatalogProgram.h"
#include "Database.h"
#include "Relation.h"


class Interpreter {
    DatalogProgram* datalog;
    Database* database;


public:
    Interpreter(DatalogProgram* datalog);
    void addTuple();
    void addHeader();
    Relation* doQuery(Predicate* query);
    std::string queryString(Predicate* query);
    void doQueries();

};


#endif //PROJECT1_INTERPRETER_H
