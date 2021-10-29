//
// Created by james on 10/26/2021.
//

#include "Relation.h"

Relation::Relation(std::string name, Header* header) {
    this->name = name;
    this->header = header;
}

std::string Relation::toString(std::vector<std::string> order, std::map<std::string, int> location) {
    std::string output = "";
    // std::cout << "in to string" << std::endl;
        for (Tuple t : tuples){
            // std::cout << "in to tuple loop" << std::endl;

            output += "  ";
            for (int i = 0; i < static_cast<int>(header->values.size()); i++){
                output += order.at(i);
                output += "=";
                output += t.values.at(location.at(order.at(i)));
                output += ", ";
            }
            output.pop_back();
            output.pop_back();
            output += "\n";
        }
        return output;
    }




void Relation::addTuple(Tuple tuple) {
    tuples.insert(tuple);
}

Relation* Relation::select(Relation *relation, Predicate *&query, int count) {
    std::string name = relation->name;
    Relation* newRelation = new Relation(name, relation->header);

    int index = 0;
    int count2 = count;
    for (int i = 0; i < static_cast<int>(query->parameters.size()); i++){
        if (query->parameters.at(i)->isConstant() == true){
            if(count2 > 0){
                count2--;
                continue;
            }
            index = i;
            for (Tuple t : relation->tuples){
                if (t.values.at(index) == query->parameters.at(index)->getParameter()){
                    newRelation->addTuple(t);
                }
            }
            break;
        }
    }
    //query->parameters.erase(query->parameters.begin() + index);
    //std::cout << "newRelation is a go" << std::endl;
    //std::cout << newRelation->toString() << std::endl;
    return newRelation;
}

Relation* Relation::selectDuplicates(Relation *relation, Predicate *&query) {
    int index1;
    int index2;
    bool found = false;
    Relation* newRelation = new Relation(relation->name, relation->header);
    for (int i = 0; i < static_cast<int>(query->parameters.size()); i++){
        if (query->parameters.at(i)->isConstant() == false){
            for (int j = i + 1; j <static_cast<int>(query->parameters.size()); j++){
                if(query->parameters.at(j)->getParameter() == query->parameters.at(i)->getParameter()){
                    index1 = i;
                    index2 = j;
                    found = true;
                    for (Tuple t : relation->tuples){
                        if (t.values.at(index1) == t.values.at(index2)){
                            newRelation->addTuple(t);
                        }
                    }
                    break;
                }
            }
        }
        if (found == true) {
            break;
        }
    }

    //std::cout << "Duplicate is a go" << std::endl;
    //std::cout << newRelation->toString() << std::endl;
    return newRelation;
}

Relation* Relation::project(Relation *relation, Predicate *&query, std::map<std::string, int> variables, std::vector<std::string> order) {
    Header* newHeader = new Header();
    for (int i = 0; i < static_cast<int>(order.size()); i++) {
        newHeader->values.push_back(order.at(i));
    }

    Relation* newRelation = new Relation(query->namePredicate, newHeader);
    for (Tuple t : relation->tuples){
        Tuple newTuple;
        for (auto itr = variables.begin(); itr != variables.end(); itr++){
            for (int i = 0; i < static_cast<int>(header->values.size()); i++) {
                newTuple.values.push_back(t.values.at(variables.at(order.at(i))));
            }
        }
        newRelation->addTuple(newTuple);
    }
    //std::cout << "project is a go" << std::endl;
    //std::cout << newRelation->toString() << std::endl;
    return newRelation;
}