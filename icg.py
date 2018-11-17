#! /usr/bin/env python
from __future__ import print_function
import logging
import os
import sys

if os.environ.get('DEBUG'):
    logging.basicConfig(level=logging.DEBUG)
else:
    logging.basicConfig(level=logging.INFO)

class TokenType:
    id = "id"
    number = "number"
    relop = "relop"
    addop = "addop"
    mulop = "mulop"
    assignment = "assignment"
    delimiter = "delimiter"
    reserved = "reserved"

class Token:

    def __init__(self, type, value):
        self.type = type
        self.value = value

    def __repr__(self):
        return "Token('%s', '%s')" % (self.type, self.value)

    def __str__(self):
        return self.value

    def __eq__(self, other):
        if self.type != other.type:
            return False

        if self.type in (TokenType.id, TokenType.number):
            return self.type == other.type

        if (self.type in (TokenType.relop, TokenType.addop, TokenType.mulop) and
            self.value == "@ny" or other.value == "@ny"):
            return self.type == other.type

        return self.type == other.type and self.value == other.value

    def __ne__(self, other):
        return not self.__eq__(other)

RESERVED_WORDS = (
    "int", "void", "if", "else", "while", "return", "read", "write"
)

def index_if(iterable, predicate):
    for i, element in enumerate(iterable):
        if predicate(element):
            return i
    return None

VOID_TOKEN = Token(TokenType.reserved, "void")
INT_TOKEN = Token(TokenType.reserved, "int")
IF_TOKEN = Token(TokenType.reserved, "if")
RETURN_TOKEN = Token(TokenType.reserved, "return")
ELSE_TOKEN = Token(TokenType.reserved, "else")
WHILE_TOKEN = Token(TokenType.reserved, "while")
COMMA_TOKEN = Token(TokenType.delimiter, ",")
SEMICOLON_TOKEN = Token(TokenType.delimiter, ";")
OPEN_PAREN_TOKEN = Token(TokenType.delimiter, "(")
CLOSE_PAREN_TOKEN = Token(TokenType.delimiter, ")")
OPEN_BRACE_TOKEN = Token(TokenType.delimiter, "{")
CLOSE_BRACE_TOKEN = Token(TokenType.delimiter, "}")
ID_TOKEN = Token(TokenType.id, "")
ASSIGNMENT_TOKEN = Token(TokenType.assignment, "=")
NUMBER_TOKEN = Token(TokenType.number, "")
REL_OP_TOKEN = Token(TokenType.relop, "@ny")
ADD_OP_TOKEN = Token(TokenType.addop, "@ny")
MUL_OP_TOKEN = Token(TokenType.mulop, "@ny")
READ_TOKEN = Token(TokenType.reserved, "read")
WRITE_TOKEN = Token(TokenType.reserved, "write")

OP_PRECEDENCE = {
    '>': 0,
    '<': 0,
    '==': 0,
    '+': 1,
    '-': 1,
    '*': 2,
    '/': 2,
    '(': 3
}

# Character groups used for the finite state machine
whitespace = " \t\n"
lowercase = "abcdefghijklmnopqrstuvwxyz"
uppercase = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
letters = lowercase + uppercase
digits = "0123456789"
add_operators = tuple("+-")
mul_operators = tuple("*/")
rel_operators = tuple(list("><") + ["=="])
all_operators = tuple(add_operators + mul_operators + rel_operators)
assignment_operators = ("=",)
delimiters = tuple("(){};,")
unitary = (add_operators + mul_operators + rel_operators + assignment_operators +
           delimiters)

class FiniteStateMachine:

    def __init__(self):
        self.transitions = {}
        self.initial_state = None
        self.current_state = None

    def set_initial_state(self, state_name):
        self.initial_state = state_name
        self.reset()

    def reset(self):
        self.current_state = self.initial_state

    def add_transition(self, from_state, to_state, activator):
        if from_state not in self.transitions:
            self.transitions[from_state] = {}
        self.transitions[from_state][activator] = to_state

    def transition(self, activator):
        next_state = self.transitions[self.current_state][activator]
        self.current_state = next_state

class LexicalAnalyzer:

    def __init__(self, transitions_dict):
        self.fsm = FiniteStateMachine()
        self.fsm.set_initial_state("start")
        for from_state in transitions_dict:
            for activator_string, to_state in transitions_dict[from_state].iteritems():
                for activator in activator_string:
                    self.fsm.add_transition(from_state, to_state, activator)

    def parse(self, source):
        token_stream = []
        production_value = ""

        skip_one = False

        for i, char in enumerate(source):
            if skip_one:
                skip_one = False
                continue

            previous_state = self.fsm.current_state
            self.fsm.transition(char)
            current_state = self.fsm.current_state

            production_ready = (
                (current_state == "start" and current_state != previous_state) or
                (current_state == "unitary")
            )

            if production_ready:
                if previous_state != "start":
                    type_ = TokenType.id
                    is_reserved = production_value in RESERVED_WORDS

                    if previous_state == "number":
                        type_ = TokenType.number
                    elif is_reserved:
                        type_ = TokenType.reserved

                    token_stream.append(Token(type_, production_value))

                if current_state == "unitary":
                    type_ = TokenType.addop

                    if char in mul_operators:
                        type_ = TokenType.mulop
                    elif char in rel_operators:
                        type_ = TokenType.relop
                    elif char in assignment_operators:
                        # Check for another = in which case it is relop ==
                        if len(source) >= (i+1) and source[i+1] == '=':
                            type_ = TokenType.relop
                        else:
                            type_ = TokenType.assignment
                    elif char in delimiters:
                        type_ = TokenType.delimiter

                    if type_ == TokenType.relop and char == '=':
                        token_stream.append(Token(type_, '=='))
                        skip_one = True
                    else:
                        token_stream.append(Token(type_, char))
                    self.fsm.reset()

                production_value = ""

            elif current_state != "start":
                production_value += char

        return token_stream

class IntermediateCodeGenerator:

    def __init__(self, tokens):
        self.tokens = tokens
        self.indent = 0 
        self.consumed_tokens = []
        self.next_label = 1
        self.next_temp = 1
        self.last_label = None
        self.last_temp = None

    def generate_code(self):
        # Only functions can exist at the outermost scope of the program.
        # Since we know the program is correct, we just expand functions
        # untill we run out of tokens
        while self.tokens:
            self.expand_function()

    def expand_function(self):
        logging.debug("expand_function first=%r" % self.first_token())

        type_ = self.consume_token()
        func_name = self.consume_token()
        open_paren = self.consume_token()

        self.expand_arguments()

        close_paren = self.consume_token()

        self.produce_triplet("entry", func_name.value)
        self.indent += 1

        self.expand_compound_statement()

        if func_name.value == "main":
            self.produce_triplet("return")

        self.indent -= 1
        self.produce_triplet("exit", func_name.value)

    def expand_arguments(self):
        # Expand arguments of the form
        # void
        # type argname
        # type argname, type argname, ...
        # Knows when to stop when the first closing parenthesis is encountered
        logging.debug("expand_arguments first=%r" % self.first_token())

        if self.first_token() == VOID_TOKEN:
            self.consume_token()
            return
        else:
            while self.first_token() != CLOSE_PAREN_TOKEN:
                type_ = self.consume_token()
                arg_name = self.consume_token()

                if self.first_token() == COMMA_TOKEN:
                    self.consume_token()

    def expand_compound_statement(self):
        # compound-stmt -> { local_declarations stament-list }
        logging.debug("expand_compound_statement first=%r" % self.first_token())
        open_brace = self.consume_token()

        self.expand_local_declarations()

        if self.first_token() == CLOSE_BRACE_TOKEN:
            self.consume_token()
            return

        self.expand_statement_list()

        close_brace = self.consume_token()

    def expand_local_declarations(self):
        logging.debug("expand_local_declarations first=%r" % self.first_token())

        while self.first_token() in (INT_TOKEN, VOID_TOKEN):
            type_ = self.consume_token()
            var_name = self.consume_token()
            semicolon = self.consume_token()

    def expand_statement_list(self):
        # statement-list only appears in the production
        # compound-stmt -> { local-declarations statement-list }
        # so we know it is delimited by a '}'
        logging.debug("expand_statement_list first=%r" % self.first_token())

        while self.first_token() != CLOSE_BRACE_TOKEN:
            self.expand_statement()

    def expand_statement(self):
        logging.debug("expand_statement first=%r" % self.first_token())

        if self.first_token() == IF_TOKEN:
            self.expand_selection_statement()
        elif self.first_token() == RETURN_TOKEN:
            self.expand_return_statement()
        elif self.first_token() == WHILE_TOKEN:
            self.expand_iteration_statement()
        elif self.first_token() == OPEN_BRACE_TOKEN:
            self.expand_compound_statement()
        elif (self.first_token() in (ID_TOKEN, READ_TOKEN, WRITE_TOKEN) and
              self.nth_token(2) == OPEN_PAREN_TOKEN):
            self.expand_call()
        else:
            self.expand_expression_statement()

    def expand_selection_statement(self):
        logging.debug("expand_selection_statement first=%r" % self.first_token())

        if_ = self.consume_token()
        open_paren = self.consume_token()

        temp = self.expand_expression()

        close_paren = self.consume_token()

        else_label = self.get_label()

        self.produce_triplet("if_false", temp, "goto", else_label)
        self.indent += 1

        if self.first_token() == OPEN_BRACE_TOKEN:
            self.expand_compound_statement()
        else:
            self.expand_statement()

        avoid_else_label = None
        if self.first_token() == ELSE_TOKEN:
            avoid_else_label = self.get_label()
            else_ = self.consume_token()

        if avoid_else_label:
            self.indent -= 1
            self.produce_triplet("goto", avoid_else_label)
            self.indent += 1

        self.indent -= 1
        self.produce_triplet("Label", else_label)
        self.indent += 1

        if avoid_else_label:
            if self.first_token() == OPEN_BRACE_TOKEN:
                self.expand_compound_statement()
            else:
                self.expand_statement()
            self.indent -= 1
            self.produce_triplet("Label", avoid_else_label)
            self.indent += 1

        self.indent -= 1

    def expand_expression_statement(self):
        logging.debug("expand_expression_statement first=%r" % self.first_token())
        temp = self.expand_expression()
        semicolon = self.consume_token()
        return temp

    def expand_expression(self, final_temp=None):
        logging.debug("expand_expression first=%r" % self.first_token())
        if (self.first_token() == ID_TOKEN and
            self.nth_token(2) == ASSIGNMENT_TOKEN):

            var = self.consume_token()
            equals = self.consume_token()

            if (self.first_token() == READ_TOKEN):
                self.produce_triplet("read", var.value)
            else:
                right_expression_temp = self.expand_expression()
                self.produce_triplet(var.value, "=", right_expression_temp)
                return var.value

        else:
            return self.expand_simple_expression(final_temp)
 
    def expand_simple_expression(self, final_temp=None):
        logging.debug("expand_simple_expression first=%r" % self.first_token())

        # An expression ends when an unbalanced parenthesis is encountered
        # or a comma ","
        # Create a postfix list of tokens in the expression
        postfix = []
        operators = []
        open_paren_counter = 0

        temp = None

        while not (self.first_token() == CLOSE_PAREN_TOKEN and
                   open_paren_counter == 0):

            if self.first_token() == COMMA_TOKEN: break
            if self.first_token() == SEMICOLON_TOKEN: break

            if (self.first_token() == ID_TOKEN and
                self.nth_token(2) == OPEN_PAREN_TOKEN):
                    temp = self.expand_expr_call()
                    postfix.append(temp)
                    continue

            if self.first_token() in (REL_OP_TOKEN, ADD_OP_TOKEN, MUL_OP_TOKEN,
                                      OPEN_PAREN_TOKEN, CLOSE_PAREN_TOKEN):

                op_token = self.consume_token()
                op = op_token.value

                if op == '(':
                    open_paren_counter += 1

                if len(operators) == 0:
                    operators.append(op)
                elif op == ")":
                    while True:
                        if operators[-1] == '(':
                            operators.pop()
                            break
                        postfix.append(operators.pop())
                    open_paren_counter -= 1
                elif OP_PRECEDENCE[op] > OP_PRECEDENCE[operators[-1]]:
                    operators.append(op)
                elif OP_PRECEDENCE[op] == OP_PRECEDENCE[operators[-1]]:
                    if op != '(':
                        postfix.append(operators.pop())

                    operators.append(op)
                else:
                    while operators and (OP_PRECEDENCE[op] <
                                         OP_PRECEDENCE[operators[-1]]):
                        if operators[-1] == '(':
                            break
                        postfix.append(operators.pop())
                    if operators and (OP_PRECEDENCE[op] ==
                                      OP_PRECEDENCE[operators[-1]]):
                        if operators[-1] != '(':
                            postfix.append(operators.pop())
                    operators.append(op)
            else:
                operand_token = self.consume_token()
                postfix.append(operand_token.value)

        while operators:
            postfix.append(operators.pop())

        # Generate code for expression by looking for the first operand 
        # in the postfix list, creating a triplet for it and its two
        # preceding operands, storing that in a temporary variable and
        # inserting the temporary variable in place of the triplet
        # in the postfix list
        if len(postfix) == 1:
            temp = self.get_temp()
            left = postfix[0]
            if final_temp:
                self.produce_triplet(final_temp, "=", left)
            else:
                self.produce_triplet(temp, "=", left)
        else:
            while set(postfix) & set(all_operators):
                first_op_i = index_if(postfix, lambda x: x in all_operators)
                temp = self.get_temp()
                left = postfix[first_op_i - 2]
                op = postfix[first_op_i]
                right = postfix[first_op_i - 1]

                if len(postfix) == 3 and final_temp:
                    self.produce_triplet(final_temp, "=", left, op, right)
                else:
                    self.produce_triplet(temp, "=", left, op, right)

                postfix = postfix[:first_op_i - 2] + [temp] + postfix[first_op_i + 1:]

        return temp

    def expand_return_statement(self):
        logging.debug("expand_return_statement first=%r" % self.first_token())
        return_ = self.consume_token();
        return_value = self.expand_expression()
        semicolon = self.consume_token();
        self.produce_triplet("return", return_value)

    def expand_call(self):
        logging.debug("expand_call first=%r" % self.first_token())
        func = self.consume_token()

        open_paren = self.consume_token()

        if func.value != "write":
            self.produce_triplet("begin_args")

        if func.value == "write":
            self.expand_args(register=False)
            self.produce_triplet("write", self.last_temp)
            return

        num_args = self.expand_args()
        return_temp = self.get_temp()

        self.produce_triplet(return_temp, "=", "call", func.value, str(num_args))

        close_paren = self.consume_token()
        semicolon = self.consume_token()
        return return_temp

    def expand_expr_call(self):
        logging.debug("expand_expr_call first=%r" % self.first_token())
        func = self.consume_token()
        open_paren = self.consume_token()

        self.produce_triplet("begin_args")
        num_args = self.expand_args()

        return_temp = self.get_temp()
        self.produce_triplet(return_temp, "=", "call", func.value, str(num_args))

        close_paren = self.consume_token()
        return return_temp

    def expand_args(self, register=True):
        logging.debug("expand_args first=%r" % self.first_token())
        arg_count = 0
        while self.first_token() != CLOSE_PAREN_TOKEN:
            expr_temp = self.expand_expression()

            if register:
                self.produce_triplet("param", expr_temp)

            if self.first_token() == COMMA_TOKEN:
                self.consume_token()

            arg_count += 1

        return arg_count

    def expand_iteration_statement(self):
        logging.debug("expand_iteration_statement first=%r", self.first_token())
        while_ = self.consume_token()
        open_paren = self.consume_token()

        num_tokens_before_condition = len(self.consumed_tokens)
        condition_temp = self.expand_expression()
        condition_tokens = self.consumed_tokens[num_tokens_before_condition:]

        close_paren = self.consume_token()

        exit_while_label = self.get_label()
        reenter_while_label = self.get_label()
        self.produce_triplet("Label", reenter_while_label)
        self.produce_triplet("if_false", condition_temp, "goto", exit_while_label)
        self.indent += 1

        if self.first_token() == OPEN_BRACE_TOKEN:
            self.expand_compound_statement()
        else:
            self.expand_statement()

        # Trigger recalculating of while condition by expanding
        # condition expression again
        self.tokens = condition_tokens + [CLOSE_PAREN_TOKEN] + self.tokens
        self.expand_expression(condition_temp)
        self.consume_token() # Consume dummy ) delimiter

        self.indent -= 1

        self.produce_triplet("goto", reenter_while_label)
        self.produce_triplet("Label", exit_while_label)

    # frontier

    def produce_triplet(self, a, b="", c="", d="", e=""):
        print(" "*4*self.indent + " ".join((a, b, c, d, e)))

    def consume_token(self):
        token = self.tokens[0]
        self.tokens = self.tokens[1:]
        self.consumed_tokens.append(token)
        return token

    def first_token(self):
        return self.tokens[0] if len(self.tokens) else None

    def nth_token(self, n):
        return self.tokens[n-1] if len(self.tokens) >= n else None

    def put_back_token(self):
        self.tokens = [self.consumed_tokens.pop()] + self.tokens

    def get_label(self):
        label = "L" + str(self.next_label)
        self.last_label = label
        self.next_label += 1
        return label

    def get_temp(self):
        temp = "t" + str(self.next_temp)
        self.last_temp = temp
        self.next_temp += 1
        return temp

if __name__ == '__main__':
    transitions_map = {
        "start": {
            whitespace: "start",
            letters: "id",
            digits: "number",
            unitary: "unitary"
        },
        "id": {
            whitespace: "start",
            letters: "id",
            digits: "id",
            unitary: "unitary"
        },
        "number": {
            whitespace: "start",
            letters: "error",
            digits: "number",
            unitary: "unitary"
        }
    }

    source_file = sys.argv[1]

    source = None

    with open(source_file) as fhandle:
        source = fhandle.read()

    lexical_analyzer = LexicalAnalyzer(transitions_map)

    tokens = lexical_analyzer.parse(source)

    codegen = IntermediateCodeGenerator(tokens)

    codegen.generate_code()
