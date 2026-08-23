######### BEGINNING OF CODE #############

"""
Programming Language Application
Rohan Bahl
ICS3U
6/6/2023

This application encodes and provides executing services for a novel programming language decvised by the author. A text-based input provides a large functionality, and auxillary files are available for further action. The program is composed of two main parts - a client side and server side component. The user initiates the application by running the program, and then follows the instructions on the text-based input. It is possible to login to 'adminstrator' privileges, which permit one extra possibilities, including looking at the error log, etc.

The main purpose of this program is to demonstrate the language. Users can enter instances of the language, and they will be executed, and the result displayed, on the console. A specifically marked 'input' box allows the user to enter their input, the 'output' box displays the result of the language, including the print stream and final result, while an error trace displays any errors encountered dueing the program's execution.


An overall description of the application is provided in the README.md file
This program only works in versions above python 3.10
To learn more about the language rules, visit LanguageRules.txt file
To understand how the compiler works, visit CompilerWorkings.txt file
To view some example scripts, visit the ExampleScripts.txt file
To practice writing some code, visit the Sandbox.txt file
"""

# Dependencies
from math import floor as fl 
from math import ceil as ce

from datetime import datetime as dt
import hashlib as passhash
import sys as system

# Special functions which are always recognized by the program and will be automatically executed (they always exist, program-independent). A combination of these functions can yield any possible boolean circuit, and is hence Turing-Complete.

SPECIAL_FUNCTIONS = [
  '~',  # -1 for less than, 0 for equal, 1 for greater than, numerical comparison operator
  '_',  # Returns the integer character corresponding to the position in the number
  '$',  # Returns the floor and ceiling of the function depending on whether the second argument is pos. or neg.  
  '+',  # Numerical addition
  '-',  # Subtraction
  '*',  # Multiplication
  '/',  # Division, throws error upon division by zero
  '^',  # Exponentiation
  '%',  # Modulus operator (a mod b), remainder of dividing a by b
  '=',  # Equals operator (NOT assignment)
  '#'   # Input-entering function
]  

ERROR_LIST = {1:'Compilation error', 2:'Runtime error', 3:'Does not halt', 4:'Unexpected input', 5:'Other error'} # Possible errors encountered by the user
ERROR_LOG = {} # The log to store any errors found by the user, is written to the ending file upon the application closing.

SEPARATOR_LENGTH = 8 # The separator length for formatting the console
# Login values
PASSWORD_HASHED = '38717b5161c2e817020a0933e1836dd0127bdef59732d77daca20ccfbf61a7ae' # The sha256 hashed value of the default admin login password
NUM_PERMITTED_TRIES = 10 # The number of attempts a user is allowed to make to enter the admin account

# Fundamental symbols for the language
DEFAULT_ARGUMENT_VALUE = 0 # The default argument value a function is set to, if it has no assignment
COMMENT_SYMBOL = '\\' # The starting character for a comment. All characters after this symbol and in the same line are considered comments
OPENING_BRACKET = '(' # The beginning of the arguments in a function definition or call must start with this character
CLOSING_BRACKET = ')' # The arguments in the function definition or function call must end with this character
VARIABLE_ASSIGNMENT_OPERATION = '-->' # The operation which is used in a variable assignment or definition
FUNCTION_ARGUMENT_SEPARATOR = ',' # The character symbol used to separate arguments in a function

CORRECT_IFSTMT_EXECUTION_VALUE = 0.0 # The if statement will be executed at this value

# Valid character sequences for instructions
RETURN_CHARACTER_COMMAND = 'R' # The valid instruction for a return statement
PRINT_CHARACTER_COMMAND = 'P' # The valid instruction for a print statement
KEYWORD_INSTRUCTION_SEPARATOR = ' ' # All arguments to the print and return character commands are separated by a space

STARTING_FUNCTION_FOR_SCRIPT = 'main' # The function from which the script shall be executed

# Valid starting and ending character sequence for if statements
CORRECT_IFSTMT_STARTING_CHARACTERS = 'I|' # All if statements must begin with 'I|'
CORRECT_IFSTMT_ENDING_CHARACTERS = '|J' # All if statements must end with '|J'

# Valid starting and ending character sequence for function definitions
CORRECT_FUNCTION_STARTING_CHARACTERS = 'S|' # All functions must begin with 'S|'
CORRECT_FUNCTION_ENDING_CHARACTERS = '|E' # All functions must end with '|E'

# Valid if start and end
isValidIfStart = lambda line: line[0] == CORRECT_IFSTMT_STARTING_CHARACTERS[0] and line[1] == CORRECT_IFSTMT_STARTING_CHARACTERS[1] # Line must begin with 'I|'
isValidIfEnd = lambda line: line[-1] == CORRECT_IFSTMT_ENDING_CHARACTERS[-1] and line[-2] == CORRECT_IFSTMT_ENDING_CHARACTERS[-2] # Line must end with '|J'

# Valid function start and end
isValidFuncStart = lambda line: not len(line) < 2 and line[0] == CORRECT_FUNCTION_STARTING_CHARACTERS[0] and line[1] == CORRECT_FUNCTION_STARTING_CHARACTERS[1] # Line must start with 'S|'
isValidFuncEnd = lambda line: not len(line) < 2 and line[-1] == CORRECT_FUNCTION_ENDING_CHARACTERS[-1] and line[-2] == CORRECT_FUNCTION_ENDING_CHARACTERS[-2] # Line must end with '|E'

# More complex utility helper methods

def breakDownIntoFunctions(lines):  # Break down the function lines into different components, extracting the name and arguments.
  """
  Arguments: lines, a list of strings, each string denoting a line of the code body
  Outputs: A list of lists, corresponding to a function. The first element of each sublist is the function definition
  
  How it works:
  Given a function body, it iterates over each line. When it reaches a function start, it creates a list to store 
  the lines of the function. Upon reaching a function end, it appends this list to a major list containing the 
  series of functions and their code, and begins a new list to store the next function, when reached. According to 
  the rules of the language, a function may not be defined within a function, so for any valid code, all functions will have 
  their proper sublists.
  """
  body = []  # The body containing the list of functions
  currFunc = None  # The specified function from which code will be added
  withinFunc = False  # Whether the specified line is in or out of a function
  for line in lines: # Iterate over each line
    if isValidFuncStart(line):  # If the line represents a valid function
      if withinFunc:  # If a function is defined within a function, we cannot allow it
        raise SyntaxError('Cannot have function in function')
      else:
        currFunc = []  # Begin a new list to hold the function and its lines in
        withinFunc = True  # Update, now we are within a function
    if withinFunc:  # This code will automatically add the function definition if true, due to its position
      currFunc.append(line)
    if isValidFuncEnd(line):
      if not withinFunc:  # Cannot have a function end when no function defined
        raise Exception('Cannot have function end when no function defined')
      else:
        # Create a new copy of the function body, add it to the categorized functions, and reiterate for next function
        currFuncCopy = currFunc
        body.append(currFuncCopy)
        withinFunc = False
        currFunc = []  # Reset to a new list for the next function
  return body  # A list of lists, each sublist corresponding to a function

def breakIntoComponents(funcDef):  # Breaks the function into a name and a series of arguments.
  """
  Arguments: A string, corresponding to the definition line of a function
  Outputs: A name, the specified function name, and a series of arguments, the variable names in the definition, all set to 0

  How it works: 
This method first extracts the name from the function by iteratively removing subsequent characters and aggregating them in a string, until a '(' is reached, which designates the start of the arguments. Since, according to the language rules, the last character is a ')', specifying the end of the arguments. By removing the '(' and ')' symbols at ends of the (currently so far) string, we may split the list around the commas. After removing all unnecessary whitespace, we obtain the variable names, and create a variable table (of dictionary type) to store their names and values, set to zero by default.
  """
  assert isValidFuncStart(funcDef)  # Assumes the argument is a valid function definition, i.e. begins with 'S|'
  funcDefCopy = funcDef[len(CORRECT_FUNCTION_STARTING_CHARACTERS):] # Make a copy to operate on, removing the definition sequence
  assert funcDefCopy[-1] == CLOSING_BRACKET  # The function definition must end with a closing ')' for the arguments

  # Extract the name from the function
  name = ''
  index = 0

  for i in funcDefCopy:# Iterate over the character in the function definition copy
    if i == OPENING_BRACKET: # We've reached the beginning of the arguments
      break
    else:
      # Append the character to the name and increment the index for the next round
      name+=i
      index+=1 

  # Extract the part corresponding to the arguments, excluding the last ')' and the first '(' to obtain a list
  args = funcDefCopy[index:] # The function's arguments, without the name
  assert args[0] == OPENING_BRACKET and args[-1] == CLOSING_BRACKET # Make sure the function encapsulates the argument body within brackets --> could replace with "args[-1:1] == ')('"
  args = args[1:-1] # Remove the two brackets, not required anymore
  argLists = args.split(FUNCTION_ARGUMENT_SEPARATOR) # Split the argument lists at the comma
  varNames = {}  # The dictionary to contain all argument names and their values
  for i in argLists:
    if i.isspace() or i == '':  # Due to the grammatical structure of the arguments, the last element of the split on the comma will be empty. For this reason, we remove the last element to preserve only the arguments.
      break
    i = i.strip()  # Remove all unecessary starting and trailing spaces
    varNames[i] = DEFAULT_ARGUMENT_VALUE  # Set them to zero, by default (they will likely be changed by a calling function when needed)
  return name, varNames  # Returns the name and the variable names, the latter packaged in a dictionary

def runScript(lines, argValues, codeBody, varTabTmp, inIfStmt):  # This is equivalent to running script equivalent to a function
  """
  Script running function:

  Arguments:
    - lines --> the lines of this script
    - argValues --> the argument values begin with
    - codeBody --> the larger code piece (to execute further from)
    - varTabTmp --> the temporary variable table (the function table maintained) in the if statement
    - inIfStmt --> whether the script is within an if statement (for which slightly different procedures must be taken)

  Outputs:
    - resultVariable, resultVarTable, returnStmtExecuted
      - Whether a return statement is executed, i.e. the function containing the script has terminated
      - The result from the execution of the script, or (0) if no result obtained
      - The resulting variable table (updated via operations)
  """
  varTable = {}  # The variable table to store all variables for the duration of execution of the script
  defName = lines[0]
  #print(lines[0]) Debugging
  #print(isValidFuncStart(defName)) Debugging
  assert isValidIfStart(defName) or isValidFuncStart(defName) # This script runner executes only if statements and functions
  # Preparation for execution of a function
  lines = lines[1:-1] # In both cases, we don't require the lines to contain the start or ending characters, we can execute without them.
  if isValidFuncStart(defName):  # Perform the necessary work if the code body executed is a function
    name, args = breakIntoComponents(defName) # Extract the name and argument values from this function definition
    argNamesForVarTable = []
    for i in args:
      argNamesForVarTable.append(i)
     # The function start must be the one specified
    for i in range(len(argValues)):  # By default, set the argument values to the base variables (either from a call function or debugging purposes)
      varTable[argNamesForVarTable[i]] = argValues[list(argValues.keys())[i]]  # Or possibly with argValues[i]. Also, this code is to transfer the values of the arguments in the calling function, to the corresponding arguments (by index) in this function. The name can change, but the value remains the same. 'argNamesForVarTable' denotes the argument names of this function.
  # Preparation for execution of the if statement
  if isValidIfStart(defName):  # Code to deal with executing an if statement
    varTable = varTabTmp  # The base variable table is the temporary table (set by the if statement in this case)
  returnStmtExecuted = False  # Has a return statement been executed? For a function, it must be, for an if statement, not necessarily
  if len(lines) == 0:  # There is no code to execute
    if inIfStmt: # If we are within an if statement which has no lines to execute, do nothing
      return DEFAULT_ARGUMENT_VALUE, varTable, True
    else:
      raise SyntaxError('Function must have return statement.')
  withinIfStmt = False # Whether we have executed another if statement in the script so far
  ifLines = [] # The lines for the if statement
  numBalanced = 0 # To ensure the brackets in the if statements are balanced. Simulates a stack of if statements
  for line in lines:  # Execute the code line by line
    if len(line) == 0 or line[0] == COMMENT_SYMBOL: # Skip lines of no instructions, or with a comment
      continue
    # Code to deal with if statement
    if isValidIfStart(line.strip()): # We have reached an if statement within the script 
      withinIfStmt = True
      numBalanced += 1 # Increment by one to designate another opening if statement structure
    if withinIfStmt:
      ifLines.append(line) # Add the lines to apend to the execution of the if statement
    if isValidIfEnd(line.strip()):  # At the end of the if statement's scope, execute the line
      numBalanced -= 1 
      if numBalanced < 0: # Unbalanced if statements 
        raise SyntaxError('Unbalanced if statements')
      if numBalanced == 0:
        withinIfStmt = False
        # Isolate the variable in the scope of the if statement
        # The specified character must be a variable ornumerical value
        keyIfLine = ifLines[0][len(CORRECT_IFSTMT_STARTING_CHARACTERS):] # Remove the starting 'I|' definition
        keyIfLine = keyIfLine.strip() # Strip of all whitespaces to extract true value
        specialVal = special(keyIfLine) # Could the specified characters be a number
        tmp = specialVal if not specialVal == None else varTable[keyIfLine]
        toExecuteIfStmt = (float(tmp) == CORRECT_IFSTMT_EXECUTION_VALUE) # Whether the specified if statement evaluates to zero
        if toExecuteIfStmt:  # Execute the statement if an only if the variable evaluates to zero, i.e. is true
          res, varTableFin, returnStmtExec = runScript(ifLines, {}, codeBody, varTable, True)
          # Execute all lines in the if statement, with no arguments (to test ifLines or ifLines[1:-1], removing the first and last two lines)
          if returnStmtExec:
            return res, varTableFin, True
          varTable = varTableFin  # Set the new and modified var table after if statement execution
          ifLines = []
        else:
          ifLines = []
          continue
        # Set the if statement lines to none again, for the next round

    if not withinIfStmt: 
      if line in CORRECT_IFSTMT_ENDING_CHARACTERS: # We acknowledge the end of the if statement
        continue
      # As long as we are not in an if statement, at an if statement, just collect the lines, execute it later
      # Start, end, or no line functions are not executed
      # Probably redundant
      if line == 'START':  # If 'START' designates the starting instruction, then skip it
        continue
      if line == '':  # If there is no line, skip it as well
        continue
      if line == 'END':  # If there is an ending statement, end the execution
        return None

      # Code to handle an instructional statement (print or return)
      isInstructionalStmt = line.split(' ')  # The return statement has two parts separated by a space
      baseInstruction = isInstructionalStmt[0] # The basic instruction, if there. Must be either print or return instruction

      # Dealing with return or if statement
      if baseInstruction == RETURN_CHARACTER_COMMAND or baseInstruction == PRINT_CHARACTER_COMMAND:  # Make sure it follows the Return 'varName' format
        assert len(isInstructionalStmt) == 2 # Can only contain instruction and specified variable
        specified_value = isInstructionalStmt[1].strip() # Returned value
        isSpecial = special(specified_value)
        toAct = isSpecial if not isSpecial == None else varTable[specified_value]
        if baseInstruction == RETURN_CHARACTER_COMMAND: # Since we are returning a return character command, return true (return statement did execute)
          return toAct, varTable, True
        else:
          print(toAct) # Print the specified value in the return statement
      else:
        # Code to handle assignment cases, including variable assignments and function calls
        parts = line.split(VARIABLE_ASSIGNMENT_OPERATION)  # Split the line based on the assignment operator
        left = parts[0].strip()  # Left side designates the variable name, cannot have whitespace
        if ' ' in left:
          raise SyntaxError('Variable must not have spaces in name')
        right = parts[1].strip()
        if right[0] not in SPECIAL_FUNCTIONS:  # If there is a variable assignment statement or function call statement
          value = special(right) # What if it's a variable assignment?
          rightTmp = right.strip()
          res = None
          if value == None and rightTmp in varTable: # If the rightTmp variable is in the function
            res = varTable[rightTmp]
          if not value == None:  # If the value is a numerical value
            varTable[left] = value
          elif not res == None:  # If the right side is a referenced variable
            varTable[left] = res
          else:
            hasName = ''
            for i in right: # Find the function name
              if i == OPENING_BRACKET:
                break
              else:
                hasName += (i + '')
            functionInit = find_function_in(hasName, codeBody)
            funcLines = []
            toStartAdding = False
            for i in codeBody: # Get all the lines corresponding to the function
              if i == functionInit:
                toStartAdding = True
              # if i == 'E': Correct backup code
              if toStartAdding:
                funcLines.append(i)
              if i == CORRECT_FUNCTION_ENDING_CHARACTERS and toStartAdding:
                break
            if not functionInit == None:
              name, args = breakIntoComponents(functionInit) # The argument names of the function
              tmp = right[len(hasName):][1:-1]  # Remove the name from the function body, 'right' and discard the first and last characters, the '(' and ')' brackets.
              parts = tmp.split(FUNCTION_ARGUMENT_SEPARATOR)
              parts = parts[:-1] # The values of the calling results
              argvals = {}
              ctr = 0 # Variable to act as placeholder (temporary for the passing of arguments to the function
              for i in args: # Assign the function argument values in the call to the designated argument names
                possible_code = parts[ctr]
                elem = special(possible_code)
                argvals[i] = elem if not elem == None else varTable[possible_code]
                ctr+=1
              value, dummy_table, retStmtExec = runScript(funcLines, argvals, codeBody, [], False)
            varTable[left] = value
        else:  # If there is a special function call statement
          symbol = right[0] # Extract first symbol
          if not right[1] == OPENING_BRACKET or not right[-1] == CLOSING_BRACKET:
            raise SyntaxError('Function definition does not contain balanced brackets immediately following symbol, and ending in them')
          right = right[1:-1]  # Remove unnecessary braces which are guaranteed to be the starting and ending characters
          arguments = right.split(FUNCTION_ARGUMENT_SEPARATOR)  # Separate into arguments
          
          # First and last components of arguments are unnecessary, formatting issue, so delete them.
          # Required due to quirk in language rules, can easily be accounted for
          del arguments[-1] # Remove last empty space
          arguments[0] = arguments[0][1:] # Since starting brace occupies first character of first argument, remove it as well
          # There can only be two arguments in a special function, so we take the first to be the left side, and the second to be the right
          # Extract the two values, compuute the sepcial function, and update the associated variable in the variable table
          firstVariable = arguments[0]
          secondVariable = arguments[1]
          firstVar = special(firstVariable)
          secondVar = special(secondVariable)
          firstVar = firstVar if not firstVar == None else varTable[firstVariable]
          secondVar = secondVar if not secondVar == None else varTable[secondVariable]
          final = special_function(symbol, firstVar, secondVar)
          varTable[left] = final
  if inIfStmt:
    return 0, varTable, returnStmtExecuted
  if not inIfStmt and not returnStmtExecuted:
    raise Exception('Return statement in function not executed')
  else: 
    return

def special(number):  # If the input is a number, it returns the numeric value, otherwise it returns None, possibly specifying this might be a variable. 
  """
  Returns whether the number is a numeric value
  Inputs: number, a string or number 
  Outputs: None, if the number does not represent a real number value, or the number value it represents
  How it works: This slightly differs from the Python float() function, as it also accepts numbers which have a single decimal point at the end, but no digit following it
  """
  if number.isnumeric():
    return float(number)
  elif number.count('.') == 1 and number[-1] == '.':  # If the number has a decimal place at the end and nothing following
    return float(number[:-1]) # Remove the last decimal place and try again
  else:  # Invalid argument, cannot be a number
    return None

def special_function(funcName, firstVar, secondVar):  # Execute one of the designated 'special functions', which can be found in 'SPECIAL_FUNCTIONS' list
  """
  Function name: special_function
  Arguments: 
    - funcName, a symbol pertaining to one of the functions needed to be executed
    - firstVar, the first argument
    - secondVar, the second argument
    (In the language, all special functions have two arguments)

  Outputs: A number, designating the result of executing the special functions
  How it works: This function works by finding the corresponding operation to the symbol. It then performs the pertained action and returns the result.
  """
  
  # Use simpler letters for easy reference
  a = firstVar
  b = secondVar

  # Each if case corresponds to a symbol in the list of special functions
  # NOTE: MATCH CASE ONLY WORKS IN PYTHON 3.10 AND ABOVE, COMPILING IT IN A LOWER VERSION OF PYTHON MAY RESULT IN FAILURE TO SUCCESSFULLY DO SO
  match funcName: # Return the appropriate result depending on the operator and arguments invoked
    case '~':
      return 1 if a > b else -1 if a < b else 0
    case '_':
      astr = str(a).split('.')
      left = astr[0] # The Integer part of the number
      right = astr[1] # The Decimal part of the number
      # 0 is to obtain the decimal value, any other integer designates the position in the representation of the number given a value-one offset. Since b at zero will designate the decimal position, it is assumed the value is never zero. A positive value designates zero and a negative value designates 1.
      list = None
      assert not b == 0 # the zero index would mean returning the decimal place
      if b > 0:
        list = left
      if b < 0:
        list = right
        b = -b
      b-=1
      return int(list[int(len(list)-1-b)])
    case '$':
      return fl(a) if b < 0 else ce(a)
    case '+':
      return a + b
    case '-':
      return a - b
    case '*':
      return a * b
    case '/':
      return a / b
    case '%':
      return a % b
    case '^':
      return a ** b
    case '=':
      return 0 if a == b else 1
    case '#': 
      num = input()
      valid = special(num)
      if valid == None:
        raise ValueError('Cannot enter string, only number.')
      else:
        return valid
    case _: # Default case with invalid function
      raise Exception('Function not special')
      
def find_function_in(funcName, functions):  # Returns the function name at the first specified occurence of the function name in the code body
  """
  Finding function:
  
  Finds a function in the list of functions. 
  Arguments: 
    funcName --> the name of the function to search for
    functions --> the list of lists, each one representing a function

  Returns: 
      function --> the function and function lines associated with the function name within list of functions

  How it works:

  For all functions in the function lists, it searches for a function list with the defined name. If such a name is found, it returns the first function appearing along the code body (so it is order dependent), otherwise throws an error, as no function is found.
  """
  for function in functions:  # Iterate over each function categorization
    definition = function
    if isValidFuncStart(definition):
      name, args = breakIntoComponents(definition)
      if funcName == name:
        return function
  raise NameError('No function with name: "'+ funcName +'" found')
  
def isFunctionCall(callBody):  # Return whether the line constitutes a function call
  """
  Inputs: callBody, the line (presumably) denoting the function call
  Outputs: Boolean, denoting whether the line possibly represents the call body

  This function first finds the index of the opening arguments, and then the index of the closing ones (the function definition or call must end with it). It then checks to make sure there isn't any other brackets within the arguments.
  This is a necessary criterion, but not sufficient, for a function call.
  """
  firstChar = callBody.find(OPENING_BRACKET) + len(OPENING_BRACKET) # Index of first char after opening bracket
  # Explanation
  # if callBody[-1] == ')' and '(' not in callBody[firstChar:-2] or ')' not in callBody[firstChar:-2]:
  #   return True
  # else:
  #   return False
      
  # callBody[-1] == ')', function ends with bracket
  # '(' not in callBody[firstChar:-2] --> There is no starting bracket within argument definition
  # ')' not in callBody[firstChar:-2] --> There is no ending bracket within argument definition
  return (callBody[-1] == CLOSING_BRACKET) and (OPENING_BRACKET not in callBody[firstChar:-2]) and (CLOSING_BRACKET not in callBody[firstChar:-2])

def execute(codeBody):  # Executes the code body inputted by the user
  """
  Code body execution function
  Arguments: codeBody, the lines of code denoting the script to be executed
  Outputs: result_number, the final result of the executed script

  How it works: This function removes all starting ';' characters, and all unnecessary spaces. It finds the designated starting function, and begins to execute from there. The final result of the starting function is returned.
  """
  codeBody = codeBody[:-1] # Remove "START" character
  for i in range(len(codeBody)):# Remove all unnecessary whitespace from the start and end of line --> Language requirements do not specify the neessity of leading or trailing whitespaces.
    line = codeBody[i]
    line = line.strip()
    if len(line) == 0: 
      raise SyntaxError('Cannot have empty line')
    line = line[1:].strip() # Replace the function body with a new line stripped of whitespace and a semicolon.
    codeBody[i] = line
  a = find_function_in(STARTING_FUNCTION_FOR_SCRIPT, codeBody)
  lines = []
  enabled = False
  for line in codeBody:
    if line == a:
      enabled = True
    if enabled:
      lines.append(line)
    if isValidFuncEnd(line) and enabled:
      break
  funcLines = lines
  name, args = breakIntoComponents(a)
  # Run the script with the given function lines,arguments, code body (for further reference), no variable table (starting with main), and not in if statement
  result_number, varTable, returnStmtExecuted = runScript(funcLines, args, codeBody, {}, False) # We run the function with the main function lines, no arguments, the required code body, an empty variable table, and not within an if statement. In this call, varTabTmp = {} and toExecIfStmt = False are dummy arguments
  
  return result_number

def parse():  # Function to parse and categorize the input code
  """
  Language parsing function
  Does not take in any arguments, but asks user to input successive lines. Then it returns the inputted values as in a code format.
  Inputs: None
  Outputs: A list denoting the lines of the inputted code body
  """

  line = 'START' # The starting line, by default
  list = [] # The list to store lines of code
  while not line == '': # Keep asking user for lines to input until they stop entering them
    line = input() 
    list.append(line) # Due to the placement of the appending function AFTER the input is asked for, the list does not contain the initialized value of the line
  listCopy = [] # Copy of list to store all non-space values
  
  for line in list: # Add all lines to the list which are not composed of only spaces
    if not line.isspace():
      listCopy.append(line) 
  list = listCopy # Set the list to the (modified) list
  return list


### CLIENT_SIDE CODE ###

def application():
  """
  The main application function
  Inputs: None
  Outputs: None

  This function serves as the entry to the client-side application. From here, via a text-based console, the user has access to many functions.
  """
  COMMANDS = [
              'l', # Login to adminstrator console
              'c', # Do some coding
              'h', # Go to the help center
             ]
  print('\n\nWelcome! This is a simple programming language application.\n')
  print('To log into the adminstrator console, enter "l".')
  print('To do some coding, enter "c".')
  print('To visit the help center, press "h".')
  print('To quit, press anything else.\n\n')
  choice = input('Please enter your main console action: ')
  while choice in COMMANDS: # While true --> delibrately event loop
    adminLogin() if choice == 'l' else doCoding() if choice == 'c' else goToHelp() if choice == 'h' else doNothing() # Add doNothing function for better formatting
    choice = input('\nPlease enter your main console action: ')
  # Write all errors logged to the error file
  file = open('Errors.txt', 'w')
  for error in ERROR_LOG:
    file.write('Error code: '+str(error)+', details: '+str(ERROR_LOG[error]))
  file.close()
  print('Thank you for using the application!\nExiting')
  return

def doNothing(): return # Do nothing dummy function

def adminLogin():
  """
  Adminstrator login function

  Inputs: None
  Outputs: None

  This function serves as the login site to the adminstrator console. It allows a set number of tries to login, and prevents the user from trying again after a certain number of tries.
  """
  print('\nThis is the adminstrator login site. You have '+ str(NUM_PERMITTED_TRIES)+ ' tries to enter the password.')
  successfulLogin = False
  for i in range(NUM_PERMITTED_TRIES):
    choice = str(input('Enter your password: '))
    hashedVal = passhash.sha256(choice.encode('utf-8')).hexdigest()
    if hashedVal == PASSWORD_HASHED:
      successfulLogin = True
      break
    else:
      print('Wrong password.')
  if not successfulLogin:
    print('\nSorry! You used too many tries, please try again later\n')
  else:
    print('\nSuccessful login\n')
    adminConsole()

def adminConsole():
  """
  The Adminstrator console
  Inputs: None
  Outputs: None

  Function: The purpose of this function is to serve as an admisntrator console for the user. Once the user has logged on to the console, they are granted access to admin privileges, such as viewing the error log. They also have the option the change the login password.
  """
  global PASSWORD_HASHED # The (new) hashed password
  ADMIN_ACTIONS = ['c', # Change password
                   'r', # View error log
                   'e'  # Exit
                  ]
  print('\nWelcome to the adminstrator console:')
  action = input('To change the password, type "c", to view the error log, press "r", otherwise press anything else to exit: ')
  while action in ADMIN_ACTIONS: # Non admin-action serves as an exit
    if action == 'c': # Change to new password 
      successfulPasswordEntry = False # Whether the user has confirmed their password by adding it a second time
      while not successfulPasswordEntry:
        newPass = input('\nPlease enter your new password: ')
        verifyPhrase = input('Please enter it once more: ')
        if newPass == verifyPhrase:
          hashedVal = passhash.sha256(newPass.encode('utf-8')).hexdigest() # Use hash value of password
          PASSWORD_HASHED = hashedVal
          print('\nSuccessfully changed password.\n')
          successfulPasswordEntry = True  
        else:
          print("New password and verify string don't match, please try again.")
    if action == 'r': # View error log
      print('\nError log:')
      for i in ERROR_LOG:
        print('\t'+str(i)+': '+ str(ERROR_LOG[i]))
    if action == 'e': # Exit admin console
      break
    action = input('\nPlease enter another action: ')
  print('Exiting admin console\n\n')
  return
  
def doCoding(): # Coding function
  """
  Coding application
  Inputs: None
  Outputs: None

  This function contains the code for entering and then delegating to execute, the user's entered code. It also allows the user to report an error pertaining to the execution or compilation of the code, and exit whenever wanted.
  """
  SEP = '_'*SEPARATOR_LENGTH # The number of underscores to format the input and exit console
  exitIndicator = False # Whether the user wants to stop coding
  while not exitIndicator: # Keep asking user after every round until they want to exit
    # Accept code, execute it, and print result
    print('\n\n'+SEP+'INPUT YOUR CODE HERE'+SEP+'\n\n')
    lines = parse()
    try:
      print('\n\n'+SEP+'OUTPUT'+SEP+'\n\n')
      result = execute(lines)
      print('Final result: '+ str(result))
      print('\n'+SEP+SEP+'\n')
    except: # Print any error messages from the function execution
      stacktrace = system.exc_info()
      print('Error message:\n'+str(stacktrace[1])+'\n\n'+SEP+SEP)
    nextAction = input('Please enter (e) if you want to exit, (r) to report an error, and (re) to report an error and exit: ') # Ask if the user wants to continue
    if 'r' in nextAction: # 'r' means the user wants to report an error
      reportError()  
    exitIndicator = True if 'e' in nextAction else False # 'e' means the user wants to exit
  print('Thank you for using the coding application.') # Ending message
  return 

def goToHelp():
  """
  Help function

  Arguments: None
  Outputs: None

  This function serves as the initial starting point to the help center. From here, the user can choose to either learn the language, or report an error.
  """
  print('\nWelcome to the help center.')
  choice = ''
  while not choice == 'l' and not choice == 'r':
    choice = input('To learn the language, press "l", press "r" to report an error. press anything else to exit: ')
  learnLang() if choice == 'l' else reportError() if choice == 'r' else doNothing()

def learnLang():
  """
  Language learning function
  Inputs: None
  Outputs: None 

  Function: The purpose of this function is to provide the user useful resources relating to the language, programs, and compilers.
  """
  print('\nTo learn the language, visit the "Language Rules" file.')
  print('To view some example programs, visit the "Example Scripts" file.')
  print('To learn how the compiler works, visit the "Compiler Workings" file.')
  print('You can always use the "Sandbox" file to practice writing the code, and put it into the console to run\n')
  return

def reportError(): # The error reporting function
  """
  Error reporting function
  Arguments: None
  Task: To receive any errors from the user and append the explanation to the persistence log
  Outputs: None
  """
  print('\nPlease select one of the error types:\n')
  for index in ERROR_LIST: # List out all the ERRORS and return them
    print(str(index)+': '+ ERROR_LIST[index])
  print('\n')
  choice = '' # Index number of error encountered by user
  while not choice in range(1, len(ERROR_LIST)+1): # Accept a number from the range of ERRORS
    choice = int(input('Please enter a number corresponding to the choices: '))  
  errorName = ERROR_LIST[choice] # Find the corresponding error and return it
  logTime = dt.now().strftime("%d/%m/%Y %H:%M:%S") # Time that error was recorded formatted in day-month-year-time format
  specificDescription = input('Please enter any further information about the problem: ')
  ERROR_LOG[choice] = (logTime, errorName, specificDescription) # Add a tuple containing the time,type of error(from the options given), and the user's specific description of the problem.
  print('Error logged successfully\n')
  return 

if __name__ == '__main__': # Main function
  application()




