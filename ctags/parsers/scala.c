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

static void parseBlock (lexerState *lexer, boolean delim, int kind, vString *scope);

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

/* Write the lexer's current token to string, taking care of special tokens */
static void writeCurTokenToStr (lexerState *lexer, vString *out_str)
{
	switch (lexer->cur_token)
	{
		case TOKEN_IDENT:
			vStringCat(out_str, lexer->token_str);
			break;
		case TOKEN_STRING:
			vStringCat(out_str, lexer->token_str);
			break;
		case TOKEN_WHITESPACE:
			vStringPut(out_str, ' ');
			break;
		case TOKEN_LSHIFT:
			vStringCatS(out_str, "<<");
			break;
		case TOKEN_RSHIFT:
			vStringCatS(out_str, ">>");
			break;
		case TOKEN_RARROW:
			vStringCatS(out_str, "->");
			break;
		default:
			vStringPut(out_str, (char) lexer->cur_token);
	}
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
static int advanceToken (lexerState *lexer, boolean skip_whitspace)
{
	printf("Advancing token...\n");
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
	advanceToken(lexer, TRUE);
}

static void deInitLexer (lexerState *lexer)
{
	vStringDelete(lexer->token_str);
	lexer->token_str = NULL;
}

static void addTag (vString* ident, const char* type, const char* arg_list, int kind, unsigned long line, MIOPos pos, vString *scope, int parent_kind)
{
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
		advanceToken(lexer, TRUE);
	}
}

/* Skips type blocks of the form <T:T<T>, ...> */
static void skipTypeBlock (lexerState *lexer)
{
	if (lexer->cur_token == '<')
	{
		skipUntil(lexer, NULL, 0);
		advanceToken(lexer, TRUE);
	}
}

/* Essentially grabs the last ident before 'for', '<' and '{', which
 * tends to correspond to what we want as the impl tag entry name */
static void parseQualifiedType (lexerState *lexer, vString* name)
{
	while (lexer->cur_token != TOKEN_EOF)
	{
		if (lexer->cur_token == TOKEN_IDENT)
		{
			if (strcmp(lexer->token_str->buffer, "for") == 0
				|| strcmp(lexer->token_str->buffer, "where") == 0)
				break;
			vStringClear(name);
			vStringCat(name, lexer->token_str);
		}
		else if (lexer->cur_token == '<' || lexer->cur_token == '{')
		{
			break;
		}
		advanceToken(lexer, TRUE);
	}
	skipTypeBlock(lexer);
}

/* Skip the body of the macro. Can't use skipUntil here as
 * the body of the macro may have arbitrary code which confuses it (e.g.
 * bitshift operators/function return arrows) */
static void skipMacro (lexerState *lexer)
{
	int level = 0;
	int plus_token = 0;
	int minus_token = 0;

	advanceToken(lexer, TRUE);
	switch (lexer->cur_token)
	{
		case '(':
			plus_token = '(';
			minus_token = ')';
			break;
		case '{':
			plus_token = '{';
			minus_token = '}';
			break;
		case '[':
			plus_token = '[';
			minus_token = ']';
			break;
		default:
			return;
	}

	while (lexer->cur_token != TOKEN_EOF)
	{
		if (lexer->cur_token == plus_token)
			level++;
		else if (lexer->cur_token == minus_token)
			level--;
		if (level == 0)
			break;
		advanceToken(lexer, TRUE);
	}
	advanceToken(lexer, TRUE);
}

static ScalaKind getTokenKind(lexerState* lexer)
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

/*
 * Rust is very liberal with nesting, so this function is used pretty much for any block
 */
static void parseBlock (lexerState *lexer, boolean delim, int kind, vString *scope)
{

	while (lexer->cur_token != TOKEN_EOF)
	{
		printf("Reading token : '%s'\n", lexer->token_str->buffer);
		ScalaKind tokenKind = getTokenKind(lexer);

		switch(tokenKind)
		{
			case K_NONE:
				printf("Ignoring token ...\n");
				// Just ignore
				advanceToken(lexer, TRUE);
				break;

			case K_PACKAGE:
				scanWhitespace(lexer);
				scanPackageName(lexer);
				if (lexer->token_str->length > 0)
					addTag(lexer->token_str, NULL, NULL, tokenKind, lexer->line, lexer->pos, scope, K_NONE);
				break;

			default:
				// all the other cases are the same
				advanceToken(lexer, TRUE);
				if (lexer->cur_token == TOKEN_IDENT)
				// otherwise it is an error, so we add no tag at all
					addTag(lexer->token_str, NULL, NULL, tokenKind, lexer->line, lexer->pos, scope, K_NONE);
				break;

		}

		/*if (tokenKind == K_NONE)
		{
			printf("Ignoring token ...\n");
			// Just ignore
			advanceToken(lexer, TRUE);
		}
		else
		{
			// Token has been recognized
			advanceToken(lexer, TRUE);

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
