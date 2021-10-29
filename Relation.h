//
// Created by james on 10/26/2021.
//

#ifndef RELATION_H
#define RELATION_H
#include "Header.h"
#include "Tuple.h"
#include "Predicate.h"
#include <string>
#include <set>
#include <iostream>
#include <map>

class Relation {
public:
    Relation(std::string name, Header* header);
    std::string name;
    Header* header;
    std::set<Tuple> tuples;
    void addTuple(Tuple tuple);
    std::string toString(std::vector<std::string> order, std::map<std::string, int> location);
    Relation* select(Relation* relation, Predicate* &query, int count);
    Relation* selectDuplicates(Relation* relation, Predicate* &query);
    Relation* project(Relation* relation, Predicate* &query, std::map<std::string, int> variables, std::vector<std::string> order);
private:




};


#endif //PROJECT1_RELATION_H
