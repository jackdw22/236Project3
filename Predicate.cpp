//
// Created by james on 9/29/2021.
//

#include "Predicate.h"

Predicate::Predicate(std::string name, std::string type) {
    this->namePredicate = name;
    this->type = type;
}

std::string Predicate::getParameters() {

    std::string output = "";
        for (int i = 0; i < static_cast<int>(parameters.size()) -1 ; i++){
            output +=  parameters.at(i)->getParameter() + ",";
        }
    output +=  parameters.at(parameters.size() - 1)->getParameter();

    return output;
}

void Predicate::getDomain() {
    for (int i = 0; i < static_cast<int>(parameters.size()) ; i++){
        domains.insert(parameters.at(i)->getParameter());
    }
}


void Predicate::predicateParse(std::vector<Token *>& tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "LEFT_PAREN") {
            LEFT_PAREN(tokens);
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

void Predicate::LEFT_PAREN(std::vector<Token *> &tokens) {
    tokens.erase(tokens.begin());
    try {// todo make sure that it is not a string when its in scheme and vice versa


        if ((tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID" && type != "Facts" )|| (tokens.at(0)->tokenToString(tokens.at(0)->type) == "STRING" && type != "Schemes")) {
           Parameter* para = new Parameter(tokens.at(0)->getValue());
           parameters.push_back(para);
           parameter(tokens);
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

void Predicate::parameter(std::vector<Token *>& tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "COMMA") {
            COMMA(tokens);
        }else if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "RIGHT_PAREN"){
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

void Predicate::COMMA(std::vector<Token *> &tokens) {
    tokens.erase(tokens.begin());
    try {

        if ((tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID" && type != "Facts" )|| (tokens.at(0)->tokenToString(tokens.at(0)->type) == "STRING" && type != "Schemes")) {
            Parameter* para = new Parameter(tokens.at(0)->getValue());
            parameters.push_back(para);
            parameter(tokens);
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

