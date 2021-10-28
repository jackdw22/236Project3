//
// Created by james on 9/29/2021.
//

#include "DatalogProgram.h"
DatalogProgram::DatalogProgram(){
    typeList = "";
}

std::string DatalogProgram::datalogOutput(){
    std::string lazy = "";
    std::string output = "Success!\n";

    output += "Schemes(" + std::to_string(schemes.size()) + "):\n";
    output += schemesOutput(schemes);
    output += "Facts(" + std::to_string(facts.size()) + "):\n";
    output += factsOutput(facts);
    output += "Rules(" + std::to_string(rules.size()) + "):\n";
    output += rulesOutput();
    output += "Queries(" + std::to_string(queries.size()) + "):\n";
    output += queriesOutput(queries);
    lazy += printDomain();
    output += "Domain(" + std::to_string(domain.size()) + "):\n";
    output += lazy;
    return output;
}



std::string DatalogProgram::schemesOutput(std::vector<Predicate*> predicates) {
    std::string output = "";
    for (int i = 0; i < static_cast<int>(predicates.size()); i++){
        output += "  " + predicates.at(i)->namePredicate + "(";
        output += predicates.at(i)->getParameters();
        output += ")\n";
    }
    return output;
}
std::string DatalogProgram::factsOutput(std::vector<Predicate*> predicates) {
    std::string output = "";
    for (int i = 0; i < static_cast<int>(predicates.size()); i++){
        output += "  " + predicates.at(i)->namePredicate + "(";
        output += predicates.at(i)->getParameters();
        output += ").\n";
    }
    return output;
}

std::string DatalogProgram::queriesOutput(std::vector<Predicate *> predicates) {
    std::string output = "";
    for (int i = 0; i < static_cast<int>(predicates.size()); i++){
        output += "  " + predicates.at(i)->namePredicate + "(";
        output += predicates.at(i)->getParameters();
        output += ")?\n";
    }
    return output;
}


std::string DatalogProgram::printDomain() {
    std::string output;
    for (int i = 0; i < static_cast<int>(facts.size()); i++){
        facts.at(i)->getDomain();
        std::set<std::string> :: iterator itr;
        for (itr = facts.at(i)->domains.begin(); itr != facts.at(i)->domains.end(); itr++){
            domain.insert(*itr);
        }
    }
   std::set<std::string> :: iterator itr;
   for (itr = domain.begin(); itr != domain.end(); itr++){
       output += "  " + *itr + "\n";
   }


   return output;
}

std::string DatalogProgram::rulesOutput() {
    std::string output = "";
    for (int i = 0; i < static_cast<int>(rules.size()); i++) {
        output += "  " + rules.at(i)->ruleOutput();
    }
    return output;
}


void DatalogProgram::datalogParse(std::vector<Token*>& tokens) {
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "SCHEMES"){
            Schemes(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        std::cout << "Parse" << std::endl;
    }

    return;

}

void DatalogProgram::Schemes(std::vector<Token *>& tokens) {
    typeList = "Schemes";
    tokens.erase(tokens.begin());

    try {
        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "COLON") {
            COLON(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        exit(0);
        // TODO make it print the bad token with spaces <3
    }

    return;
}
void DatalogProgram::FACTS(std::vector<Token *> &tokens) {
    typeList = "Facts";
    tokens.erase(tokens.begin());

    try {
        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "COLON") {
            COLON(tokens);
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

void DatalogProgram::RULES(std::vector<Token *> &tokens) {
    typeList = "Rules";
    tokens.erase(tokens.begin());
    try {
        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "COLON") {
            COLON(tokens);
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
void DatalogProgram::QUERIES(std::vector<Token *>& tokens) {
    typeList = "Queries";
    tokens.erase(tokens.begin());

    try {
        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "COLON") {
            COLON(tokens);
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



void DatalogProgram::COLON(std::vector<Token *> &tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID") {
            Predicate* Predicate = new class Predicate(tokens.at(0)->getValue(), typeList);
            if(typeList == "Schemes"){
                schemes.push_back(Predicate);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
            }else if(typeList == "Facts"){
                facts.push_back(Predicate);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
            }else if(typeList == "Queries"){
                queries.push_back(Predicate);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
            }else {
                Rule *Rule = new class Rule(Predicate);
                rules.push_back(Rule);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
                Rule->ruleParser(tokens);
                PERIOD(tokens);
            }
            }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "RULES") {
            RULES(tokens);
            }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "QUERIES"){
            QUERIES(tokens);
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

void DatalogProgram::endPredicate(std::vector<Token *> &tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID") {
            Predicate *Predicate = new class Predicate(tokens.at(0)->getValue(), typeList);
            if(typeList == "Schemes"){
                schemes.push_back(Predicate);
            }else if(typeList == "Facts"){
                facts.push_back(Predicate);
            }else if(typeList == "Queries"){
                queries.push_back(Predicate);
            }
            Predicate->predicateParse(tokens);
            endPredicate(tokens);
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "FACTS") {
            FACTS(tokens);
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "PERIOD" && (typeList == "Facts" || typeList == "Rules")){
            PERIOD(tokens);
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "Q_MARK" && typeList == "Queries"){
            Q_MARK(tokens);

            /* }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "RULES") {
            RULES(tokens);
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "QUERIES"){
            QUERIES(tokens);

       */}else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "COLON_DASH" &&  typeList == "Rules"){
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

void DatalogProgram::PERIOD(std::vector<Token *> &tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "QUERIES"  && typeList == "Rules") {
            QUERIES(tokens);
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID") {
            if (typeList == "Facts") {
                Predicate *Predicate = new class Predicate(tokens.at(0)->getValue(), typeList);
                facts.push_back(Predicate);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
            }else if(typeList == "Rules"){
                Predicate *Predicate = new class Predicate(tokens.at(0)->getValue(), typeList);
                Rule *Rule = new class Rule(Predicate);
                rules.push_back(Rule);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
                Rule->ruleParser(tokens);
                PERIOD(tokens);
            }
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "RULES"){
            RULES(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        exit(0);

    }

    return;
}

void DatalogProgram::Q_MARK(std::vector<Token *> &tokens) {
    tokens.erase(tokens.begin());
    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "EOF") {
            return;
        }else if(tokens.at(0)->tokenToString(tokens.at(0)->type) == "ID") {
            if (typeList == "Queries") {
                Predicate *Predicate = new class Predicate(tokens.at(0)->getValue(), typeList);
                queries.push_back(Predicate);
                Predicate->predicateParse(tokens);
                endPredicate(tokens);
            }
        }else{
            throw (505);

        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        exit(0);

    }

    return;
}

