#ifndef MST_H
#define MST_H

#include <vector>
#include <string>
#include <queue>
#include "hashtable.cpp"

using namespace std;

struct MST_Object;
typedef struct MST_Object MST_Object;

struct MST_Str;
typedef struct MST_Str MST_Str;

struct MST_SVLog;
typedef struct MST_SVLog MST_SVLog;

struct MST_Expr;
typedef struct MST_Expr MST_Expr;

struct MST_SVExpr;
typedef struct MST_SVExpr MST_SVExpr;

struct MST_ObjRef;
typedef struct MST_ObjRef MST_ObjRef;

struct MST_Lst;
typedef struct MST_Lst MST_Lst;

struct MST_Sym;
typedef struct MST_Sym MST_Sym;

struct MST_Trigger;
typedef struct MST_Trigger MST_Trigger;

struct MST_TrgTask;
typedef struct MST_TrgTask MST_TrgTask;

struct MST_Func;
typedef struct MST_Func MST_Func;

struct MST_Task;
typedef struct MST_Task MST_Task;

class MST_ClassDef;

class MST_TrgTask;
class MST_Env;

#define MST_DEF_DIM 16
#define MST_STRLEN 32

enum MST_ObjType {
  MST_Value,
  MST_Class,
  MST_Expression,
  MST_SVLogic,
  MST_ObjectReference,
  MST_SVExpression,
  MST_String,
  MST_Symbol,
  MST_SymbolReference,
  MST_List,
  MST_Function,
  nMST_Task,
  MST_ExternalFunction,
  MST_Error
};

struct MST_Object {
  void* Ptr;
  enum MST_ObjType Type;
};

struct MST_Str {
  MST_Object Object;
  int cLen;
  int mLen;
  char* Data;
};

enum MST_IOType {
  MST_Internal,
  MST_Input,
  MST_Output,
  MST_Inout
};

struct MST_SVLog {
  MST_Object Object;
  enum MST_IOType IO;
  MST_Str* Name;
  MST_Trigger* Triggers;
  int Changed;
  int Closed;
  void* Reg;
  void* Wire;
  int nScope;
  int ItemWidth;
  int nDim;
  int nItems[];
};

string AddIndent(string src, int n = 1);
MST_Object* SolveMST_Object(MST_Object* obj);
MST_SVExpr SVRefMST_Object(MST_Object* obj);
string SVDecMST_Object(MST_SVLog* obj);
int FreeMST_Object(MST_Object* obj);
MST_Object* CopyMST_Object(MST_Object* obj);
string MST_ToStr(MST_Object* obj);

MST_Str* AllocMST_Str(int l);
MST_Object* AllocMST_Val(int w);
MST_Object* AllocMST_Array(int w, vector<int> dim);
pair<MST_Object*, vector<int>> GetIndex_MSTObjRef(MST_ObjRef* ref);
int GetIntMST_Obj(MST_Object* obj);

struct MST_Val {
  MST_Object Object;
  string* ArrName;
  int ItemWidth;
  int nDim;
  int nItems[];
};

struct MST_MemRef {
  MST_Object* obj;
  uint8_t* ptr;
  int boff;
  int wid;
};

enum MST_Operator {
  MST_Set,
  MST_Add,
  MST_Sub,
  MST_Mul,
  MST_Div,
  MST_Pow,
  MST_BAnd,
  MST_BOr,
  MST_Xor,
  MST_LAnd,
  MST_LOr,
  MST_BNot,
  MST_LNot,
  MST_Equal,
  MST_NE,
  MST_Greater,
  MST_GE,
  MST_Lesser,
  MST_LE,
  MST_ShiftL,
  MST_ShiftR,
  MST_Call,
  MST_NewObj,
  MST_NewPort,
  MST_Bind,
  MST_AddTrgTask,
  MST_NewFunc,
  MST_If,
  MST_Progn,
  MST_For,
  MST_NewTask,
  MST_GetInt,
  MST_MCall
};

struct MST_Expr {
  MST_Object Object;
  enum MST_Operator Operator;
  int nOperand;
  MST_Object* Operands[];
};

MST_SVExpr SVCodeMST_Expr(MST_Expr* expr);
MST_SVExpr SVCodeMST_ExprIF(MST_Expr* expr);
MST_SVExpr SVCodeMST_ExprProgn(MST_Expr* expr);
MST_SVExpr SVCodeMST_Expr1(MST_Expr* expr);
MST_SVExpr SVCodeMST_Expr2(MST_Expr* expr);

MST_Expr* AllocMST_Expr(int n);
MST_Object* MST_Expr2(enum MST_Operator oprt, MST_Object* oprd1, MST_Object* oprd2);

int FreeMST_Expr(MST_Expr* expr);
MST_Object* MST_ObjExpr(MST_Expr* expr);
MST_Object* EvalMST_Expr(MST_Expr* expr, int sim);
int MSTOprt_1Arg(enum MST_Operator oprt, int oprd);
int MSTOprt_2Arg(enum MST_Operator oprt, int oprd1, int oprd2);

MST_MemRef MST_GetMemRef(MST_ObjRef* ref);
int MST_SetInt(MST_Object* obj, int n);

struct MST_SVExpr {
  MST_Object Object;
  string* Prev;
  string* Ref;
};

struct MST_ObjRef {
  MST_Object Object;
  MST_Object* Width;
  MST_Object* Index;
};

MST_ObjRef* AllocMST_ObjRef();

struct MST_Lst {
  MST_Object Object;
  int nItems;
  int mItems;
  MST_Object** Items;
};

MST_Lst* AllocMST_Lst(int n);
MST_Object* Push_MST_Lst(int nargs, MST_Object** args);
MST_Object* MST_ConvertListToArray(MST_Lst* lst);
MST_Object* MST_MakeArray(int nargs, MST_Object** args);

int MST_TransArglst(MST_Lst* dst, MST_Lst* src);
int MST_BindArgs(MST_Lst* arglst, int nargs, MST_Object** args);

struct MST_Func {
  MST_Object Object;
  MST_Str* Name;
  MST_Lst* Args;
  int nExpr;
  MST_Expr* Expr[];
};

MST_Func* AllocMST_Func(int nargs, int nexpr);
MST_Object* CallMST_Func(MST_Func* func, int nargs, MST_Object** args);

struct MST_Task {
  MST_Object Object;
  MST_Str* Name;
  MST_Lst* Args;
  int nExpr;
  MST_Expr* Expr[];
};

MST_Task* AllocMST_Task(int nargs, int nexpr);
MST_Object* SolveMST_Task(MST_Task* task, int nargs, MST_Object** args);

struct MST_ExFunc {
  MST_Object Object;
  MST_Str* Name;
  MST_Object* (*pFunc)(int nargs, MST_Object** args);
};

MST_ExFunc* AllocMST_ExFunc();

struct MST_Sym {
  MST_Object Object;
  MST_Object* Val;
  MST_Str* Name;
};

enum MST_Edge {
  MST_atchange,
  MST_posedge,
  MST_negedge
};

struct MST_Trigger {
  enum MST_Edge Edge;
  MST_SVLog* Log;

  MST_Trigger* LinkByLog;
  MST_Trigger* LinkByTask;

  MST_TrgTask* Task;
};

struct MST_TrgTask {
  MST_Trigger* Trg;

  int nExpr;
  MST_Expr* Expr[];
};

MST_Trigger* AddTrgMST_TrgTask(MST_TrgTask* task, enum MST_Edge edge, MST_Object* obj);
MST_Trigger* AddTrgMST_TrgTask(MST_TrgTask* task, enum MST_Edge edge, MST_SVLog* obj);
int FreeMST_TrgTask(MST_TrgTask* task);
string SVCodeMST_TrgTask(MST_TrgTask* task);
int EvalMST_TrgTask(MST_TrgTask* task);

class MST_Scope {
private:
  MST_Scope* Par;
  HashTable<MST_Object*> Table;

public:
  MST_Scope();
  MST_Scope(MST_Scope* par);
  ~MST_Scope();

  MST_Object* Get(MST_Str* str);
  int Add(MST_Str* str, MST_Object* obj);
};

class MST_Env {
private:
  vector<vector<MST_SVLog*>> Objects;
  vector<MST_TrgTask*> TrgTasks;

  vector<MST_SVLog*> Changes;
  vector<HashTable<MST_Sym*>*> Tables;
  vector<vector<MST_Sym*>> Symbols;
  vector<vector<MST_Sym*>> SpecialSym;

  vector<MST_Func*> Functions;
  vector<MST_Task*> Tasks;
  vector<MST_ExFunc*> ExFunctions;

  HashTable<MST_Object*> SVNameTable;

  vector<MST_Val*> Arrays;

  int Error;
  int Mode;

public:
  MST_Env();
  ~MST_Env();

  int AddScope();
  int CloseScope();

  MST_SVLog* AddObject(int ndim);
  MST_TrgTask* AddTrgTask(int n);
  MST_Func* AddFunction(MST_Object* name, int nargs, int nexpr);
  MST_Task* AddTask(MST_Object* name, int nargs, int nexpr);
  MST_ExFunc* AddExFunc(MST_Object* name, MST_Object* (*pfunc)(int nargs, MST_Object** args));
  MST_ExFunc* AddExFunc(char* name, MST_Object* (*pfunc)(int nargs, MST_Object** args));
  MST_ExFunc* AddExFunc(string name, MST_Object* (*pfunc)(int nargs, MST_Object** args));

  int AllocObjects();

  int NotifyChange(MST_SVLog* log);
  int WaitTask();

  int Bind(MST_Object* sym, MST_Object* obj);

  MST_Sym* GetSym(MST_Object* sym);
  MST_Object* GetSymVal(MST_Object* sym);

  MST_Sym* AddSpecialSym(MST_Object* sym, MST_Object* val);
  int DelSpecialSym();

  int BindSVName(string name, MST_Object* obj);
  int FindSVName(string name);
  int AddArray(MST_Val* array);

  int SetErrorFlag(int f);
  int GetErrorFlag();

  int SetMode(int m);
  int GetMode();

  string SVCode();
};

MST_SVLog* MST_AddObject(int ndim);
int MST_AllocObjects();

MST_TrgTask* AddTrgTask(int n);

int MST_NotifyChange(MST_SVLog* log);
int MST_WaitTask();

int MST_BindSym(MST_Object* sym, MST_Object* obj);

MST_Sym* MST_GetSym(MST_Object* sym);
MST_Object* MST_GetSymVal(MST_Object* sym);

MST_Func* AddMST_Function(MST_Object* name, int nargs, int nexpr);
MST_Task* AddMST_Task(MST_Object* name, int nargs, int nexpr);
MST_ExFunc* AddMST_ExFunc(MST_Object* name, MST_Object* (*pfunc)(int nargs, MST_Object** args));
MST_ExFunc* AddMST_ExFunc(char* name, MST_Object* (*pfunc)(int nargs, MST_Object** args));
MST_ExFunc* AddMST_ExFunc(string name, MST_Object* (*pfunc)(int nargs, MST_Object** args));

string MST_SVCode();

int MST_OpenScope();
int MST_CloseScope();

MST_Sym* MST_AddSpecialSym(MST_Object* sym, MST_Object* val);
int MST_DelSpecialSym();

int MST_BindSVName(string name, MST_Object* obj);
int MST_FindSVName(string name);

int MST_AddArray(MST_Val* array);

int MST_SetErrorFlag(int f);
int MST_GetErrorFlag();

int MST_SetMode(int m);
int MST_GetMode();

#endif
