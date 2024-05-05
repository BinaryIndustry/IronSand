#include "hashtable.cpp"
#include "mightstone.h"
#include <string>
#include <vector>
#include <variant>

enum MSTP_Oprt {
  MSTP_Set,
  MSTP_Add,
  MSTP_Sub,
  MSTP_Mul,
  MSTP_Div,
  MSTP_Pow,
  MSTP_BAnd,
  MSTP_BOr,
  MSTP_Xor,
  MSTP_LAnd,
  MSTP_LOr,
  MSTP_BNot,
  MSTP_LNot,
  MSTP_Equal,
  MSTP_NE,
  MSTP_Greater,
  MSTP_GE,
  MSTP_Lesser,
  MSTP_LE,
  MSTP_ShiftL,
  MSTP_ShiftR,

  MSTP_BracketL,
  MSTP_BracketR,
  MSTP_ParenL,
  MSTP_ParenR,
  MSTP_Space,
  MSTP_Tab,
  MSTP_NL,
  MSTP_Semicolon,
  MSTP_Comma,
  MSTP_Hex,
  MSTP_Dollar,
  MSTP_DollarEq,
  MSTP_CurlyBracketL,
  MSTP_CurlyBracketR,
  MSTP_PlusSemicolon,
  MSTP_MinusSemicolon,
  MSTP_Piriod,
  MSTP_Colon,

  MSTP_SetAdd,
  MSTP_SetSub,
  MSTP_SetMul,
  MSTP_SetDiv,
  MSTP_SetPow,
  MSTP_SetBAnd,
  MSTP_SetBOr,
  MSTP_SetXor,
  MSTP_SetLAnd,
  MSTP_SetLOr
};

enum MSTP_ResWord {
  MSTP_In,
  MSTP_Out,
  MSTP_IO,
  MSTP_At,
  MSTP_Pos,
  MSTP_Neg,
  MSTP_Defun,
  MSTP_If,
  MSTP_Else,
  MSTP_For,
  MSTP_Deftask
};

struct MSTP_TokenInfo;
typedef struct MSTP_TokenInfo MSTP_TokenInfo;

typedef struct MSTP_Token{
  MSTP_TokenInfo* Info;
  char* Pos;
  int Len;
} MSTP_Token;

typedef struct MSTP_TokenInfo {
  int OprtID;
  int WordID;
} MSTP_TokenInfo;

class MST_Parser {
private:
  HashTable<MSTP_TokenInfo*> OprtTable;
  HashTable<MSTP_TokenInfo*> WordTable;

  vector<MSTP_TokenInfo*> Operators;
  vector<MSTP_TokenInfo*> Words;

  int Error;
  int Mode;

  vector<MST_Object*> Parse2(vector<variant<MSTP_TokenInfo*, MST_Object*>>& list, int mode);

public:
  MST_Parser();
  ~MST_Parser();

  vector<MST_Object*> Parse(char* src);
};

vector<MST_Object*> MSTP_Parse(char* src);
vector<MST_Object*> MSTP_Read();

int EnableITP();
MST_Object* TimingChart(int nargs, MST_Object** args);
