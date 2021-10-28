#include "Token.h"

Token::Token(TokenType type, std::string description, int line) {
    // TODO: initialize all member variables
    this->type = type;
    this->value = description;
    this->lineNumber = line;
}

std::string Token::getValue() {
    return value;
}

std::string Token::tokenToString(TokenType type) {
    switch(type){
        case TokenType::COLON:
            return "COLON";
        case TokenType::COLON_DASH:
            return "COLON_DASH";
        case TokenType::UNDEFINED:
            return "UNDEFINED";
        case TokenType::ENDFILE:
            return "EOF";
        case TokenType::COMMA:
            return "COMMA";
        case TokenType::Q_MARK:
            return "Q_MARK";
        case TokenType::LEFT_PAREN:
            return "LEFT_PAREN";
        case TokenType::RIGHT_PAREN:
            return "RIGHT_PAREN";
        case TokenType::MULTIPLY:
            return "MULTIPLY";
        case TokenType::ADD:
            return "ADD";
        case TokenType::SCHEMES:
            return "SCHEMES";
        case TokenType::FACTS:
            return "FACTS";
        case TokenType::RULES:
            return "RULES";
        case TokenType::QUERIES:
            return "QUERIES";
        case TokenType::ID:
            return "ID";
        case TokenType::STRING:
            return "STRING";
        case TokenType::COMMENT:
            return "COMMENT";
        case TokenType::PERIOD:
            return "PERIOD";
    }
    return "hello";
}

std::string Token::print(){
    std::string output;
    output = "(" + tokenToString(type) + ",\"" + value + "\"," + std::to_string(lineNumber) + ")";
    return output;
}

