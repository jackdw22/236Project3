//
// Created by james on 9/29/2021.
//

#include "Rule.h"
Rule::Rule(Predicate *headPredicate) {
    this->headPredicate = headPredicate;
}

std::string Rule::ruleOutput() {
    std::string output = "";
    output += headPredicate->namePredicate + "(";
    output += headPredicate->getParameters() + ")";
    output += " :- ";
    for (int i = 0; i < static_cast<int>(bodyPredicates.size()) - 1; i++){
        output += bodyPredicates.at(i)->namePredicate + "(";
        output += bodyPredicates.at(i)->getParameters();
        output += "),";
    }
    output += bodyPredicates.at(bodyPredicates.size() - 1)->namePredicate + "(";
    output += bodyPredicates.at(bodyPredicates.size() - 1)->getParameters();
    output += ").\n";
    return output;
}

void Rule::ruleParser(std::vector<Token *>& tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID") {
            Predicate *Predicate = new class Predicate(tokens.at(0)->getValue(), "Rules");
            bodyPredicates.push_back(Predicate);
            Predicate->predicateParse(tokens);
            ID(tokens);
        }else{
            throw (505);
        }
    }
    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        exit(0);
    }
    return;
}

void Rule::COMMA(std::vector<Token *>& tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID") {
            Predicate *Predicate = new class Predicate(tokens.at(0)->getValue(), "Rules");
            bodyPredicates.push_back(Predicate);
            Predicate->predicateParse(tokens);
            ID(tokens);
            return;
        }else{
            throw (505);
        }
    }
    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        exit(0);
    }
    return;
}

void Rule::ID(std::vector<Token *>& tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "COMMA") {
            COMMA(tokens);
        } else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "PERIOD"){
            return;
        }else{
            throw (505);
        }
    }
    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        exit(0);
    }
    return;
}



