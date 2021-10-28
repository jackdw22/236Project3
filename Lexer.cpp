#include "Lexer.h"
#include "ColonAutomaton.h"
#include "ColonDashAutomaton.h"
#include "CommaAutomaton.h"
#include "PeriodAutomaton.h"
#include "QMarkAutomaton.h"
#include "LeftParenAutomaton.h"
#include "RightParenAutomaton.h"
#include "MultiplyAutomaton.h"
#include "AddAutomaton.h"
#include "schemesAutomaton.h"
#include "FactsAutomaton.h"
#include "RulesAutomaton.h"
#include "Queries.h"
#include "IDAutomaton.h"
#include "STRINGAUTOMATON.h"
#include "InvalidStringAutomaton.h"
#include "CommentAutomaton.h"
#include "BlockCommentAutomata.h"
#include "invalidComment.h"
#include <iostream>

Lexer::Lexer() {
       CreateAutomata();
}

Lexer::~Lexer() {
    // TODO: need to clean up the memory in `automata` and `tokens`
     /*while(!automata.empty()){
         delete automata.at(automata.size() - 1);
     }
     while(!tokens.empty()){
         delete tokens.at(tokens.size() - 1);*/
     }



void Lexer::CreateAutomata() {
    automata.push_back(new ColonAutomaton());
    automata.push_back(new ColonDashAutomaton());
    automata.push_back(new CommaAutomaton());
    automata.push_back(new PeriodAutomaton());
    automata.push_back(new QMarkAutomaton());
    automata.push_back(new LeftParenAutomaton());
    automata.push_back(new RightParenAutomaton());
    automata.push_back(new MultiplyAutomaton());
    automata.push_back(new AddAutomaton());
    automata.push_back(new schemesAutomaton());
    automata.push_back(new FactsAutomaton());
    automata.push_back(new RulesAutomaton());
    automata.push_back(new Queries());
    automata.push_back(new IDAutomaton());
    automata.push_back(new InvalidStringAutomaton());
    automata.push_back(new StringAutomaton());
    automata.push_back(new CommentAutomaton());
    automata.push_back(new BlockCommentAutomata());
    automata.push_back(new invalidComment());





    // TODO: Add the other needed automata here
}

void Lexer::Run(std::string& input) {
    // TODO: convert this pseudo-code with the algorithm into actual C++ code
    lineNumber = 1;
    while (input.size() > 0){
        maxRead = 0;
        maxAuto = automata.at(0);
        while(std::isspace(input.at(0))) {

            if (input.at(0) == '\n') {
                lineNumber++;

            }


            input.erase(0, 1);
            if (input.size() == 0) {
                break;
            }
        }

        for (auto & i : automata){
            int inputRead = i->Start(input);
            if(inputRead > maxRead){
                maxRead = inputRead;
                maxAuto = i;
            }
        }
        if (maxRead > 0){
            Token* newToken;
            newToken = maxAuto->CreateToken(input.substr(0, maxRead), lineNumber);
            lineNumber = lineNumber + maxAuto->NewLinesRead();
            if(newToken->tokenToString(newToken->type) != "COMMENT"){
                tokens.push_back(newToken);
            }

        }else if (input.size() > 0){
            maxRead = 1;
            Token * newToken = new Token(TokenType::UNDEFINED, input.substr(0, 1), lineNumber);
            tokens.push_back(newToken);

        }
        input.erase(0, maxRead);

    }
    Token * newToken = new Token(TokenType::ENDFILE, "", lineNumber);
    tokens.push_back(newToken);

   /* for(int i = 0; i < static_cast<int>(tokens.size()); i++){
        std::cout << tokens.at(i)->print() << "\n";
    }

    std::cout << "Total Tokens = " << tokens.size();
    */

    /*
    set lineNumber to 1
    // While there are more characters to tokenize
    loop while input.size() > 0 {
        set maxRead to 0
        set maxAutomaton to the first automaton in automata

        // TODO: you need to handle whitespace inbetween tokens

        // Here is the "Parallel" part of the algorithm
        //   Each automaton runs with the same input
        foreach automaton in automata {
            inputRead = automaton.Start(input)
            if (inputRead > maxRead) {
                set maxRead to inputRead
                set maxAutomaton to automaton
            }
        }
        // Here is the "Max" part of the algorithm
        if maxRead > 0 {
            set newToken to maxAutomaton.CreateToken(...)
                increment lineNumber by maxAutomaton.NewLinesRead()
                add newToken to collection of all tokens
        }
        // No automaton accepted input
        // Create single character undefined token
        else {
            set maxRead to 1
                set newToken to a  new undefined Token
                (with first character of input)
                add newToken to collection of all tokens
        }
        // Update `input` by removing characters read to create Token
        remove maxRead characters from input
    }
    add end of file token to all tokens
    */
}

