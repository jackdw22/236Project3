//
// Created by james on 9/15/2021.
//

#ifndef BLOCKCOMMENTAUTOMATA_H
#define BLOCKCOMMENTAUTOMATA_H
#include "Automaton.h"

class BlockCommentAutomata : public Automaton {
private:
    void S1(const std::string& input);
    void S2(const std::string& input);
    void S3(const std::string& input);
    void S4(const std::string& input);
public:
    BlockCommentAutomata() : Automaton(TokenType::COMMENT){}

    void S0(const std::string& input);

};


#endif //PROJECT1_BLOCKCOMMENTAUTOMATA_H
