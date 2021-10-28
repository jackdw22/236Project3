//
// Created by james on 9/28/2021.
//

#include "Parser.h"

Parser::Parser() {
    Datalog = new DatalogProgram();
}

void Parser::Parse(std::vector<Token *> tokens) {

    try {

        if (tokens.at(0)->tokenToString(tokens.at(0)->type) == "SCHEMES"){
            Datalog->datalogParse(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << "  " << tokens.at(0)->print();
        std::cout << "Parse" << std::endl;
    }
    //std::cout << Datalog->datalogOutput();
    return;
}

/*void Parser::COLON(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            Predicate* Predicate = new class Predicate(tokens.at(index)->getValue());
            if (typeList == "Schemes"){

            }
            ID(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "RULES") {
            RULES(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "QUERIES"){
                QUERIES(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "COLON" << std::endl;
    }
    return;
}


void Parser::scheme(std::vector<Token *> tokens) {
    ID(tokens);
    return;
}

void Parser::ID(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "LEFT_PAREN") {
            LEFT_PAREN(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "COMMA" || tokens.at(index)->tokenToString(tokens.at(index)->type) == "RIGHT_PAREN"){
            idList(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "ID" << std::endl;
    }
    return;
}
void Parser::LEFT_PAREN(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            ID(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "STRING"){
            STRING(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "LEFT_PAREN" << std::endl;
    }
    return;
}

void Parser::idList(std::vector<Token*> tokens) {
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "RIGHT_PAREN") {
            RIGHT_PAREN(tokens);
        } else if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "COMMA") {
            COMMA(tokens);
        } else {
            throw (505);
        }
    }
        catch(...){
            std::cout << "Failure!" << std::endl;
            std::cout << tokens.at(index)->print();
            std::cout << "idList" << std::endl;
        }
        return;
}

void Parser::COMMA(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            ID(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "STRING"){
            STRING(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "Comma" << std::endl;
    }
    return;
}

void Parser::RIGHT_PAREN(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            schemeList(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "FACTS"){
            FACTS(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "PERIOD" && (typeList == "Rules" || typeList == "Facts")){
            PERIOD(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "COLON_DASH"){
            COLON_DASH(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "COMMA" && typeList == "Rules"){
            COMMA(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "Q_MARK" && typeList == "Queries"){
            Q_MARK(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "RightParen" << std::endl;
    }
    return;
}

void Parser::schemeList(std::vector<Token *> tokens) {
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            scheme(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "FACTS"){
            FACTS(tokens);
        }else{
            throw (505);
        }
    }

    catch(...){
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "schemeList" << std::endl;
    }
    return;
}

void Parser::FACTS(std::vector<Token *> tokens) {
    index++;
    typeList = "Facts";
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "COLON") {
            COLON(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "facts!" << std::endl;

    }
    return;

}

void Parser::factList(std::vector<Token *> tokens) {
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            ID(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "RULES"){
            RULES(tokens);
        }else{
            throw (505);
        }
    } catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "stringList" << std::endl;

    }
    return;

}

void Parser::STRING(std::vector<Token *> tokens) {
   stringList(tokens);
    return;
    }
void Parser::stringList(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "COMMA") {
            COMMA(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "RIGHT_PAREN"){
            RIGHT_PAREN(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "stringList" << std::endl;

    }
    return;

}

void Parser::PERIOD(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "QUERIES"  && typeList == "Rules") {
            QUERIES(tokens);
        }else if(tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID" ||tokens.at(index)->tokenToString(tokens.at(index)->type) == "RULES"){
            factList(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "Period" << std::endl;

    }
    return;
}

void Parser::RULES(std::vector<Token *> tokens) {
    index++;
    typeList = "Rules";
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "COLON") {
            COLON(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "Rules" << std::endl;

    }
    return;
}

void Parser::ruleList(std::vector<Token *> tokens) {
    std::cout << "Rulelist" << std::endl;
}

void Parser::COLON_DASH(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID") {
            ID(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "COLON_DASH" << std::endl;

    }
    return;
}


void Parser::parameter(std::vector<Token *> tokens) {
    std::cout << "parameter" << std::endl;
}

void Parser::QUERIES(std::vector<Token *> tokens) {
    index++;
    typeList = "Queries";
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "COLON") {
            COLON(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "QUERY" << std::endl;

    }
    return;
}

void Parser::Q_MARK(std::vector<Token *> tokens) {
    index++;
    try {

        if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "EOF") {
            ENDFILE(tokens);
        }else if (tokens.at(index)->tokenToString(tokens.at(index)->type) == "ID"){
            ID(tokens);
        }else{
            throw (505);
        }
    }

    catch(...) {
        std::cout << "Failure!" << std::endl;
        std::cout << tokens.at(index)->print();
        std::cout << "Q_mark" << std::endl;

    }
    return;
}

void Parser::ENDFILE(std::vector<Token *> tokens) {
    std::cout << "Success!" << std::endl;
}*/