/*
*
*   This source code is released for free distribution under the terms of the
*   GNU General Public License version 2 or (at your option) any later version.
*
*   This module contains functions for generating tags for Scala files.
*/

/*
*   INCLUDE FILES
*/
#include "general.h"	/* must always come first */
#include "main.h"

#include <string.h>
#include <stdio.h>

#include "keyword.h"
#include "parse.h"
#include "entry.h"
#include "options.h"
#include "read.h"
#include "routines.h"
#include "vstring.h"

/*
*   MACROS
*/
#define MAX_STRING_LENGTH 256

/*
*   DATA DECLARATIONS
*/

typedef enum {
	K_CLASS,
	K_FIELD,
	K_TRAIT,
	K_METHOD,
	K_OBJECT,
	K_PACKAGE,
	K_TYPE,
	K_NONE
} ScalaKind;

static kindOption scalaKinds[] = {
	{TRUE, 'c', "class", "classes"},
	{TRUE, 'f', "field", "fields"},
	{TRUE, 't', "trait", "traits"},
	{TRUE, 'm', "method", "methods"},
	{TRUE, 'o', "object", "objects"},
	{TRUE, 'p', "package", "packages"},
	{TRUE, 'T', "type", "type aliases"}
	// add implicit ?
};

typedef enum {
	TOKEN_WHITESPACE,
	TOKEN_STRING,
	TOKEN_IDENT,
	TOKEN_LSHIFT,
	TOKEN_RSHIFT,
	TOKEN_RARROW,
	TOKEN_EOF
} tokenType;

typedef struct {
	/* Characters */
	int cur_c;
	int next_c;

	/* Tokens */
	int cur_token;
	vString* token_str;
	unsigned long line;
	MIOPos pos;
} lexerState;

/*
*   FUNCTION PROTOTYPES
*/

static void parseBlock (lexerState *lexer, boolean delim, ScalaKind topLevelKind, vString *scope);

/*
 *  DEBUG
 */

static void printCurrentToken(lexerState* lexer)
{
	switch(lexer->cur_token)
	{
		case TOKEN_WHITESPACE:
		case TOKEN_STRING:
		case TOKEN_IDENT:
			printf("%s", lexer->token_str->buffer);
			break;
		case TOKEN_LSHIFT:
			printf("<<");
			break;
		case TOKEN_RSHIFT:
			printf(">>");
			break;
		case TOKEN_RARROW:
			printf("->");
			break;
		case TOKEN_EOF:
			printf("#!EOF#!");
			break;
		default:
			printf("%c", lexer->cur_token);
			break;
	}
}

/*
*   FUNCTION DEFINITIONS
*/

/* Resets the scope string to the old length */
static void resetScope (vString *scope, size_t old_len)
{
	scope->length = old_len;
	scope->buffer[old_len] = '\0';
}

/* Adds a name to the end of the scope string */
static void addToScope (vString *scope, vString *name)
{
	if (vStringLength(scope) > 0)
		vStringCatS(scope, "::");
	vStringCat(scope, name);
}

/* Reads a character from the file */
static void advanceChar (lexerState *lexer)
{
	lexer->cur_c = lexer->next_c;
	lexer->next_c = getcFromInputFile();
}

/* Reads N characters from the file */
static void advanceNChar (lexerState *lexer, int n)
{
	while (n--)
		advanceChar(lexer);
}

/* Store the current character in lexerState::token_str if there is space
 * (set by MAX_STRING_LENGTH), and then read the next character from the file */
static void advanceAndStoreChar (lexerState *lexer)
{
	if (vStringLength(lexer->token_str) < MAX_STRING_LENGTH)
		vStringPut(lexer->token_str, (char) lexer->cur_c);
	advanceChar(lexer);
}

static boolean isWhitespace (int c)
{
	return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

static boolean isAscii (int c)
{
	return (c >= 0) && (c < 0x80);
}

/* This isn't quite right for Unicode identifiers */
static boolean isIdentifierStart (int c)
{
	return (isAscii(c) && (isalpha(c) || c == '_')) || !isAscii(c);
}

/* This isn't quite right for Unicode identifiers */
static boolean isIdentifierContinue (int c)
{
	return (isAscii(c) && (isalnum(c) || c == '_')) || !isAscii(c);
}

static boolean isPackageChar(int c)
{
	return (isAscii(c) && (isalnum(c) || c == '.')) || !isAscii(c);
}

static boolean isOpeningBracket(char c)
{
	return (c == '(' || c == '{');
}

static char closingBracketFor(char c)
{
	switch(c)
	{
		case '(':
			return ')';
		case '{':
			return '}';
		default:
			return c;
	}
}

static ScalaKind getKeywordKind(lexerState* lexer)
{
	if (lexer->cur_token == TOKEN_IDENT)
	{
		if (strcmp(lexer->token_str->buffer, "class") == 0)
		{
			return K_CLASS;
		}
		else if (strcmp(lexer->token_str->buffer, "def") == 0)
		{
			return K_METHOD;
		}
		else if (strcmp(lexer->token_str->buffer, "object") == 0)
		{
			return K_OBJECT;
		}
		else if (strcmp(lexer->token_str->buffer, "trait") == 0)
		{
			return K_TRAIT;
		}
		else if (strcmp(lexer->token_str->buffer, "val") == 0)
		{
			return K_FIELD;
		}
		else if (strcmp(lexer->token_str->buffer, "var") == 0)
		{
			return K_FIELD;
		}
		else if (strcmp(lexer->token_str->buffer, "package") == 0)
		{
			return K_PACKAGE;
		}
		else if (strcmp(lexer->token_str->buffer, "type") == 0)
		{
			return K_TYPE;
		}
		else
		{
			return K_NONE;
		}
	}
	else
	{
		return K_NONE;
	}
}

static void scanWhitespace (lexerState *lexer)
{
	while (isWhitespace(lexer->cur_c))
		advanceChar(lexer);
}

/* Normal line comments start with two /'s and continue until the next \n
 * (potentially after a \r). Additionally, a shebang in the beginning of the
 * file also counts as a line comment as long as it is not this sequence: #![ .
 * Block comments start with / followed by a * and end with a * followed by a /.
 * Unlike in C/C++ they nest. */
static void scanComments (lexerState *lexer)
{
	/* // */
	if (lexer->next_c == '/')
	{
		advanceNChar(lexer, 2);
		while (lexer->cur_c != EOF && lexer->cur_c != '\n')
			advanceChar(lexer);
	}
	/* block comment */
	else if (lexer->next_c == '*')
	{
		int level = 1;
		advanceNChar(lexer, 2);
		while (lexer->cur_c != EOF && level > 0)
		{
			if (lexer->cur_c == '*' && lexer->next_c == '/')
			{
				level--;
				advanceNChar(lexer, 2);
			}
			else if (lexer->cur_c == '/' && lexer->next_c == '*')
			{
				level++;
				advanceNChar(lexer, 2);
			}
			else
			{
				advanceChar(lexer);
			}
		}
	}
}

static void scanIdentifier (lexerState *lexer)
{
	vStringClear(lexer->token_str);
	do
	{
		advanceAndStoreChar(lexer);
	} while(lexer->cur_c != EOF && isIdentifierContinue(lexer->cur_c));
}

static void scanPackageName(lexerState* lexer)
{
	vStringClear(lexer->token_str);
	do
	{
		advanceAndStoreChar(lexer);
	} while(lexer->cur_c != EOF && isPackageChar(lexer->cur_c));
}

/* Double-quoted strings, we only care about the \" escape. These
 * last past the end of the line, so be careful not to store too much
 * of them (see MAX_STRING_LENGTH). The only place we look at their
 * contents is in the function definitions, and there the valid strings are
 * things like "C" and "Rust" */
static void scanString (lexerState *lexer)
{
	vStringClear(lexer->token_str);
	advanceAndStoreChar(lexer);
	while (lexer->cur_c != EOF && lexer->cur_c != '"')
	{
		if (lexer->cur_c == '\\' /*&& lexer->next_c == '"'*/)
			advanceAndStoreChar(lexer);
		advanceAndStoreChar(lexer);
	}
	advanceAndStoreChar(lexer);
}

/* This deals with character literals: 'n', '\n', '\uFFFF'; and lifetimes:
 * 'lifetime. We'll use this approximate regexp for the literals:
 * \' \\ [^']+ \' or \' [^'] \' or \' \\ \' \'. Either way, we'll treat this
 * token as a string, so it gets preserved as is for function signatures with
 * lifetimes. */
static void scanCharacterOrLifetime (lexerState *lexer)
{
	vStringClear(lexer->token_str);
	advanceAndStoreChar(lexer);

	if (lexer->cur_c == '\\')
	{
		advanceAndStoreChar(lexer);
		/* The \' \\ \' \' (literally '\'') case */
		if (lexer->cur_c == '\'' && lexer->next_c == '\'')
		{
			advanceAndStoreChar(lexer);
			advanceAndStoreChar(lexer);
		}
		/* The \' \\ [^']+ \' case */
		else
		{
			while (lexer->cur_c != EOF && lexer->cur_c != '\'')
				advanceAndStoreChar(lexer);
		}
	}
	/* The \' [^'] \' case */
	else if (lexer->cur_c != '\'' && lexer->next_c == '\'')
	{
		advanceAndStoreChar(lexer);
		advanceAndStoreChar(lexer);
	}
	/* Otherwise it is malformed, or a lifetime */
}

/* Advances the parser one token,  skipping whitespace
 * (otherwise it is concatenated and returned as a single whitespace token).
 * Whitespace is needed to properly render function signatures. Unrecognized
 * token starts are stored literally, e.g. token may equal to a character '#'. */
static int advanceToken (lexerState *lexer)
{
	const boolean skip_whitspace = TRUE;
	//printf("Advancing token...\n");
	boolean have_whitespace = FALSE;
	lexer->line = getInputLineNumber();
	lexer->pos = getInputFilePosition();
	while (lexer->cur_c != EOF)
	{
		if (isWhitespace(lexer->cur_c))
		{
			scanWhitespace(lexer);
			have_whitespace = TRUE;
		}
		else if (lexer->cur_c == '/' && (lexer->next_c == '/' || lexer->next_c == '*'))
		{
			scanComments(lexer);
			have_whitespace = TRUE;
		}
		else
		{
			if (have_whitespace && !skip_whitspace)
				return lexer->cur_token = TOKEN_WHITESPACE;
			break;
		}
	}
	lexer->line = getInputLineNumber();
	lexer->pos = getInputFilePosition();
	while (lexer->cur_c != EOF)
	{
		if (lexer->cur_c == '"')
		{
			scanString(lexer);
			return lexer->cur_token = TOKEN_STRING;
		}
		else if (lexer->cur_c == '\'')
		{
			scanCharacterOrLifetime(lexer);
			return lexer->cur_token = TOKEN_STRING;
		}
		else if (isIdentifierStart(lexer->cur_c))
		{
			scanIdentifier(lexer);
			return lexer->cur_token = TOKEN_IDENT;
		}
		/* These shift tokens aren't too important for tag-generation per se,
		 * but they confuse the skipUntil code which tracks the <> pairs. */
		else if (lexer->cur_c == '>' && lexer->next_c == '>')
		{
			advanceNChar(lexer, 2);
			return lexer->cur_token = TOKEN_RSHIFT;
		}
		else if (lexer->cur_c == '<' && lexer->next_c == '<')
		{
			advanceNChar(lexer, 2);
			return lexer->cur_token = TOKEN_LSHIFT;
		}
		else if (lexer->cur_c == '-' && lexer->next_c == '>')
		{
			advanceNChar(lexer, 2);
			return lexer->cur_token = TOKEN_RARROW;
		}
		else
		{
			int c = lexer->cur_c;
			advanceChar(lexer);
			return lexer->cur_token = c;
		}
	}
	return lexer->cur_token = TOKEN_EOF;
}

static void initLexer (lexerState *lexer)
{
	advanceNChar(lexer, 2);
	lexer->token_str = vStringNew();

	if (lexer->cur_c == '#' && lexer->next_c == '!')
		scanComments(lexer);
	advanceToken(lexer);
}

static void deInitLexer (lexerState *lexer)
{
	vStringDelete(lexer->token_str);
	lexer->token_str = NULL;
}

static void addTag (vString* ident, const char* type, const char* arg_list, int kind, unsigned long line, MIOPos pos, vString *scope, int parent_kind)
{
	if (parent_kind == K_NONE)
	{
		printf("Adding token KIND[%d]: %s\n", kind, ident->buffer);
	}
	else
	{
		printf("Adding token KIND[%d] >> KIND[%d]: %s\n", parent_kind, kind, ident->buffer);
	}

	if (kind == K_NONE)
		return;
	tagEntryInfo tag;
	initTagEntry(&tag, ident->buffer, &(scalaKinds[kind]));

	tag.lineNumber = line;
	tag.filePosition = pos;
	tag.sourceFileName = getInputFileName();

	tag.extensionFields.signature = arg_list;
	tag.extensionFields.varType = type;
	if (parent_kind != K_NONE)
	{
		tag.extensionFields.scopeKind = &(scalaKinds[parent_kind]);
		tag.extensionFields.scopeName = scope->buffer;
	}
	makeTagEntry(&tag);
}

/* Skip tokens until one of the goal tokens is hit. Escapes when level = 0 if there are no goal tokens.
 * Keeps track of balanced <>'s, ()'s, []'s, and {}'s and ignores the goal tokens within those pairings */
static void skipUntil (lexerState *lexer, int goal_tokens[], int num_goal_tokens)
{
	int angle_level = 0;
	int paren_level = 0;
	int brace_level = 0;
	int bracket_level = 0;
	while (lexer->cur_token != TOKEN_EOF)
	{
		if (angle_level == 0 && paren_level == 0 && brace_level == 0
		    && bracket_level == 0)
		{
			int ii = 0;
			for(ii = 0; ii < num_goal_tokens; ii++)
			{
				if (lexer->cur_token == goal_tokens[ii])
				{
					break;
				}
			}
			if (ii < num_goal_tokens)
				break;
		}
		switch (lexer->cur_token)
		{
			case '<':
				angle_level++;
				break;
			case '(':
				paren_level++;
				break;
			case '{':
				brace_level++;
				break;
			case '[':
				bracket_level++;
				break;
			case '>':
				angle_level--;
				break;
			case ')':
				paren_level--;
				break;
			case '}':
				brace_level--;
				break;
			case ']':
				bracket_level--;
				break;
			case TOKEN_RSHIFT:
				if (angle_level >= 2)
					angle_level -= 2;
				break;
			/* TOKEN_LSHIFT is never interpreted as two <'s in valid Rust code */
			default:
				break;
		}
		/* Has to be after the token switch to catch the case when we start with the initial level token */
		if (num_goal_tokens == 0 && angle_level == 0 && paren_level == 0 && brace_level == 0
		    && bracket_level == 0)
			break;
		advanceToken(lexer);
	}
}

/* tokens: { ... } x
 *         ^       ^
 *         in     out
 */
static void skipBlock(lexerState* lexer)
{
	char closing_bracket = closingBracketFor(lexer->cur_token);
	printf("<");
	printCurrentToken(lexer);
	advanceToken(lexer);
	while(lexer->cur_token != EOF && lexer->cur_token != closing_bracket)
	{
		printCurrentToken(lexer);
		printf(", ");
		if (isOpeningBracket(lexer->cur_token))
		{
			skipBlock(lexer);
		}
		else
		{
			advanceToken(lexer);
		}
	}
	printf("%c>\n", lexer->cur_token);
	advanceToken(lexer);
}

/* Finds and move to the next occurence of the given character
 * If a keyword is found before the given character or the
 * end of the file is reached, returns false
 */
static boolean findNext(lexerState* lexer, int toFind)
{
	while (lexer->cur_token != TOKEN_EOF)
	{
		if (lexer->cur_token == toFind)
		{
			return TRUE;
		}
		else if (getKeywordKind(lexer) != K_NONE)
		{
			return FALSE;
		}
		else
		{
			advanceToken(lexer);
		}
	}
	return FALSE;
}

static boolean findArgList(lexerState* lexer)
{
	while (lexer->cur_token != TOKEN_EOF)
	{
		if (lexer->cur_token == '(')
		{
			return TRUE;
		}
		else if (getKeywordKind(lexer) != K_NONE || lexer->cur_token == '{')
		{
			return FALSE;
		}
		else
		{
			advanceToken(lexer);
		}
	}
	return FALSE;
}

static void parseArgList(lexerState* lexer, const ScalaKind top_level_kind, vString* scope)
{
	advanceToken(lexer);  // skip the opening '('
	while(lexer->cur_token != TOKEN_EOF && lexer->cur_token != ')')
	{
		// parse the argument
		// skip val or var token
		if (getKeywordKind(lexer) == K_FIELD)
		{
			advanceToken(lexer);
		}

		if (lexer->cur_token == TOKEN_IDENT)
		{
			addTag(lexer->token_str, NULL, NULL, K_FIELD, lexer->line, lexer->pos, scope, top_level_kind);
		}
		else
		{
			return;
		}

		// find the next one
		while (lexer->cur_token != TOKEN_EOF && lexer->cur_token != ',' && lexer->cur_token != ')')
		{
			if (isOpeningBracket(lexer->cur_token))
			{
				skipBlock(lexer);
			}
			else
			{
				advanceToken(lexer);
			}
		}
		if (lexer->cur_token == ',')
			advanceToken(lexer);
	}
}

/* As objects, classes and traits are very similar, we parse them the same way
 * class A (argList) ... { body }
 * ^^^^^                        ^
 *  in                         out
 */
static void parseClassLike(lexerState* lexer, ScalaKind kind, vString* scope)
{
	printf("Parsing class-like of kind %d\n", kind);
	advanceToken(lexer);

	if (lexer->cur_token != TOKEN_IDENT)
		return; // error, there should be the class name

	// add the corresponding tag
	vString* class_name = vStringNewCopy(lexer->token_str);
	addTag(class_name, NULL, NULL, kind, lexer->line, lexer->pos, scope, K_NONE);

	const size_t scope_length = scope->length;
	addToScope(scope, class_name);

	// parse the argument list, if any is found
	// TODO there may be more than one argList: class AB (a:a)(implicit b:B)
	boolean foundArgList = findArgList(lexer);
	if (foundArgList)
	{
		//advanceChar(lexer);
		//advanceToken(lexer); // we need to skip the first '{' and enter the block
		parseArgList(lexer, kind, scope);
	}

	// parse the block of the class like, if any is found
	boolean foundBlock = findNext(lexer, '{');
	printf("Found block: %d\n", foundBlock);
	if (foundBlock)
	{
		//advanceChar(lexer);
		advanceToken(lexer); // we need to skip the first '{' and enter the block
		parseBlock(lexer, TRUE, kind, scope);
	}
	// else nothing

	resetScope(scope, scope_length);
}


/*
 * Rust is very liberal with nesting, so this function is used pretty much for any block
 */
static void parseBlock (lexerState *lexer, boolean delim, ScalaKind topLevelKind, vString *scope)
{
	while (lexer->cur_token != TOKEN_EOF
			&& !(delim && lexer->cur_token == '}'))
	{
		printf("Reading token : \"%s\" | '%c'\n", lexer->token_str->buffer, lexer->cur_c);

		if (isOpeningBracket(lexer->cur_token))
		{
			// we skip sub-blocks
			printf("Skipping block that starts with %c\n", lexer->cur_token);
			skipBlock(lexer);
			//advanceToken(lexer);
		}
		else
		{
			ScalaKind tokenKind = getKeywordKind(lexer);

			switch(tokenKind)
			{
				case K_NONE:
					//printf("Ignoring token ...\n");
					// Just ignore
					advanceToken(lexer);
					break;

				case K_PACKAGE:
					scanWhitespace(lexer);
					scanPackageName(lexer);
					if (lexer->token_str->length > 0)
						addTag(lexer->token_str, NULL, NULL, tokenKind, lexer->line, lexer->pos, scope, K_NONE);
					break;

				case K_CLASS:
				case K_TRAIT:
				case K_OBJECT:
					parseClassLike(lexer, tokenKind, scope);
					break;

				default:
					// all the other cases are the same
					advanceToken(lexer);
					if (lexer->cur_token == TOKEN_IDENT)
					{
						addTag(lexer->token_str, NULL, NULL, tokenKind, lexer->line, lexer->pos, scope, topLevelKind);
					}
					else
					{
						if (topLevelKind != K_NONE)
							return;
						// if it is K_NONE, we don't stop parsing
					}
					break;

			}
		}

		/*if (tokenKind == K_NONE)
		{
			printf("Ignoring token ...\n");
			// Just ignore
			advanceToken(lexer);
		}
		else
		{
			// Token has been recognized
			advanceToken(lexer);

			//if (lexer->cur_token != TOKEN_IDENT)
				//return;

			if (lexer->cur_token == TOKEN_IDENT)
			// otherwise it is an error, so we add no tag at all
				addTag(lexer->token_str, NULL, NULL, tokenKind, lexer->line, lexer->pos, scope, K_NONE);
		}*/

	}
}

static void findScalaTags (void)
{
	lexerState lexer;
	vString* scope = vStringNew();
	initLexer(&lexer);

	parseBlock(&lexer, FALSE, K_NONE, scope);
	vStringDelete(scope);

	deInitLexer(&lexer);
}

extern parserDefinition *ScalaParser (void)
{
	static const char *const extensions[] = { "scala", NULL };
	parserDefinition *def = parserNewFull ("Scala", KIND_FILE_ALT);
	def->kinds = scalaKinds;
	def->kindCount = ARRAY_SIZE (scalaKinds);
	def->extensions = extensions;
	def->parser = findScalaTags;

	return def;
}

// TODO catch case `val (x, y) = ???`
// TODO handle operators (any sequence of non-space, non-identifier character): http://stackoverflow.com/questions/7656937/valid-identifier-characters-in-scala
// TODO handle `'identifier` case (why do people even do that ?)
// TODO better package reading (take into account the '.')
// TODO handle `class A(val a, val b) { }`
// TODO handle parenthesis and sub-blocks
// TODO set '[' as bracket
