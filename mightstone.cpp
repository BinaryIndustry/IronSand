#include "hashtable.cpp"
#include "mightstone.h"
#include <vector>
#include <iostream>
#include <string>
#include <queue>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <sstream>
#include <iomanip>

using namespace std;

static MST_Env* mst_env = new MST_Env;

MST_Object* SolveMST_Object(MST_Object* obj, int at) {
  if (obj->Type == MST_Expression) {
    MST_Expr* expr = (MST_Expr*)obj;
    if (at && expr->Operator == MST_For) {
      if (expr->nOperand < 2) {
        cout << "invalid expression" << endl;
        exit(-1);
      }
      if (expr->Operands[0]->Type != MST_SymbolReference) {
        cout << "error" << endl;
        exit(-1);
      }
      if (expr->Operands[1]->Type != MST_Value) {
        cout << "error" << endl;
        exit(-1);
      }
      int n = GetIntMST_Obj(expr->Operands[1]);
      MST_Object* val = AllocMST_Val(32);
      *((int*)val->Ptr) = 0;
      MST_Sym* cnt = MST_AddSpecialSym(expr->Operands[0], val);
      vector<MST_Object*> progexpr;
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < expr->nOperand - 2; j++) {
          if (expr->Operands[j+2] && expr->Operands[j+2]->Type == MST_Expression)
            progexpr.push_back(SolveMST_Object(CopyMST_Object(expr->Operands[j+2]), at));
          }
        *((int*)val->Ptr) = i+1;
        MST_BindSym((MST_Object*)cnt, val);
      }
      MST_Expr* prog = AllocMST_Expr(progexpr.size());
      prog->Operator = MST_Progn;
      for (int i = 0; i < progexpr.size(); i++) {
        prog->Operands[i] = progexpr[i];
      }
      MST_DelSpecialSym();
      FreeMST_Object(val);
      FreeMST_Object((MST_Object*)expr);
      return (MST_Object*)prog;
    }
    for (int i = 0; i < expr->nOperand; i++) {
      if (expr->Operands[i]) {
        expr->Operands[i] = SolveMST_Object(expr->Operands[i], at);
      }
    }
    if (at) {
      if (expr->Operator == MST_Bind) {
        MST_Object* ret = EvalMST_Expr(expr, 0);
        FreeMST_Object(obj);
        return ret;
      } else if (expr->Operator == MST_Set) {
        if (expr->nOperand != 2) {
          cout << "invalid expression" << endl;
          exit(-1);
        }
        if (expr->Operands[0]->Type == MST_Symbol) {
          MST_Sym* sym = (MST_Sym*)expr->Operands[0];
          if (sym->Val->Type == MST_Value) {
            expr->Operator = MST_Bind;
            MST_Object* ret = EvalMST_Expr(expr, 0);
            FreeMST_Object(obj);
            return ret;
          }
        }
      }
      for (int i = 0; i < expr->nOperand; i++) {
        if (expr->Operands[i]->Type == MST_Symbol) {
          MST_Sym* sym = (MST_Sym*)expr->Operands[i];
          if (sym->Val) {
            expr->Operands[i] = CopyMST_Object(sym->Val);
          }
        }
      }
      if (expr->Operator == MST_Call) {
        if (expr->nOperand < 1) {
          cout << "invalid expression" << endl;
          exit(-1);
        }
        if (expr->Operands[0]->Type == nMST_Task) {
          MST_Object* ret = SolveMST_Task((MST_Task*)expr->Operands[0], expr->nOperand - 1, expr->Operands+1);
          for (int i = 0; i < expr->nOperand; i++) {
            FreeMST_Object(expr->Operands[i]);
          }
          return ret;
        } else {
          cout << "invalid expression" << endl;
          exit(-1);
        }
      }
    }
    return obj;
  } else if (obj->Type == MST_SymbolReference) {
    MST_Sym* sym = MST_GetSym(obj);
    FreeMST_Object(obj);
    if (sym->Val->Type == MST_SVLogic || sym->Val->Type == MST_Value) {
      return sym->Val;
    }
    return (MST_Object*)sym;
  } else if (obj->Type == MST_List) {
    MST_Lst* lst = (MST_Lst*)obj;
    for (int i = 0; i < lst->nItems; i++) {
      if (lst->Items[i]) {
        lst->Items[i] = SolveMST_Object(lst->Items[i], at);
        if (lst->Items[i]->Type == MST_Symbol) {
          MST_Sym* sym = (MST_Sym*)lst->Items[i];
          if (sym->Val && sym->Val->Type == MST_Value) {
            lst->Items[i] = CopyMST_Object(sym->Val);
          }
        }
      }
    }
    return obj;
  } else if (obj->Type == MST_ObjectReference) {
    MST_ObjRef* ref = (MST_ObjRef*)obj;
    ref->Object.Ptr = SolveMST_Object((MST_Object*)ref->Object.Ptr, at);
    for (int i = 0; i < ref->nIndex; i++) {
      if (ref->Index[i]) {
        ref->Index[i] = SolveMST_Object((MST_Object*)ref->Index[i], at);
        if (ref->Index[i]->Type == MST_Symbol) {
          MST_Sym* sym = (MST_Sym*)ref->Index[i];
          if (sym->Val && sym->Val->Type == MST_Value) {
            ref->Index[i] = CopyMST_Object(sym->Val);
          }
        }
      }
    }
    return obj;
  } else {
    return obj;
  }
}

string AddIndent(string src, int n) {
  if (!src.size()) return "";
  string ret;
  for (int i = 0; i < n; i++)
    ret += "\t";
  for (int i = 0; i < src.size(); i++) {
    ret += src[i];
    if (src[i] == '\n' && i+1 < src.size()) {
      for (int j = 0; j < n; j++)
        ret += "\t";
    }
  }
  return ret;
}

MST_SVExpr SVRefMST_Object(MST_Object* obj) {
  if (obj->Type == MST_Expression) {
    return SVCodeMST_Expr((MST_Expr*)obj);
  } else if (obj->Type == MST_SVLogic) {
    MST_SVLog* log = (MST_SVLog*) obj;
    string* name = new string;
    MST_Str* str = log->Name;
    while (str) {
      *name += string(str->Data, str->cLen);
      str = str->Next;
    }
    if (log->nScope) {
      *name += "_" + to_string(log->nScope);
    }
    return {{NULL, MST_SVExpression}, NULL, name};
  } else if (obj->Type == MST_Value) {
    MST_Val* val = (MST_Val*)obj;
    string* ref = new string;
    if (val->ItemWidth <= 32 && val->nDim == 0) {
      *ref = to_string(GetIntMST_Obj(obj));
      return {{NULL, MST_SVExpression}, NULL, ref};
    }
    if (val->ArrName) {
      *ref = *(val->ArrName);
      return {{NULL, MST_SVExpression}, NULL, ref};
    }
    MST_AddArray(val);
    *ref = *(val->ArrName);
    return {{NULL, MST_SVExpression}, NULL, ref};
  } else if (obj->Type == MST_SymbolReference) {
    return SVRefMST_Object(MST_GetSymVal((MST_Object*)obj->Ptr));
  } else if (obj->Type == MST_ObjectReference) {
    MST_ObjRef* ref = (MST_ObjRef*)obj;
    MST_SVExpr base = SVRefMST_Object((MST_Object*)ref->Object.Ptr);
    string* refstr = base.Ref;
    string* prev = base.Prev;
    if (!refstr) {
      cout << "error" << endl;
      exit(-1);
    }
    MST_SVExpr expr = {{NULL, MST_SVExpression}, NULL, refstr};
    for (int i = 0; i < ref->nIndex; i++) {
      MST_SVExpr index = SVRefMST_Object(ref->Index[i]);
      if (!index.Ref) {
        cout << "invalid index" << endl;
        exit(-1);
      }
      if (index.Prev) {
        if (prev) {
          *prev += *(index.Prev);
        } else {
          prev = index.Prev;
        }
      }
      *refstr += "[" + *(index.Ref) + "]";
      delete index.Ref;
    }
    expr.Prev = prev;
    return expr;
  } else if (obj->Type == MST_Symbol) {
    return SVRefMST_Object(MST_GetSymVal(obj));
  } else {
    exit(-1);
  }
}

string SVDecMST_Object(MST_SVLog* obj) {
  string ret;
  if (obj->IO) {
    switch (obj->IO) {
      case (MST_Input):
        ret += "input ";
        break;
      case (MST_Output):
        ret += "output ";
        break;
      case (MST_Inout):
       ret += "inout ";
       break;
     }
  }
  ret += "logic ";
  string w;
  for (int i = 0; i < obj->nDim; i++) {
    w += "[" + to_string(obj->nItems[obj->nDim - i - 1] - 1) + ":0]";
  }
  if (obj->ItemWidth > 1) {
    w += "[" + to_string(obj->ItemWidth - 1) + ":0]";
  }
  if (w.size()) {
    ret += w + " ";
  }
  MST_Str* name = obj->Name;
  while (name) {
    ret += string(name->Data, name->cLen);
    name = name->Next;
  }
  if (obj->nScope) {
    ret += "_" + to_string(obj->nScope);
  }
  return ret;
}

int FreeMST_Object(MST_Object* obj) {
  if (obj->Type == MST_Value) {
    MST_Val* val = (MST_Val*)obj;
    if (val->ArrName) delete val->ArrName;
    free(obj);
    return 0;
  } else if (obj->Type == MST_Expression) {
    MST_Expr* expr = (MST_Expr*)obj;
    for (int i = 0; i < expr->nOperand; i++) {
      if (expr->Operands[i]) {
        FreeMST_Object(expr->Operands[i]);
      }
    }
    free(obj);
    return 0;
  } else if (obj->Type == MST_SVLogic || obj->Type == MST_Function || obj->Type == MST_Symbol || obj->Type == nMST_Task || obj->Type == MST_ExternalFunction) {
    return 0;
  } else if (obj->Type == MST_ObjectReference) {
    free(obj);
    return 0;
  } else if (obj->Type == MST_String) {
    MST_Str* str = (MST_Str*)obj;
    while (str) {
      MST_Str* fr = str;
      str = str->Next;
      free(fr);
    }
    return 0;
  } else if (obj->Type == MST_SymbolReference) {
    FreeMST_Object((MST_Object*)obj->Ptr);
    free(obj);
    return 0;
  } else if (obj->Type == MST_List) {
    MST_Lst* lst = (MST_Lst*)obj;
    for (int i = 0; i < lst->nItems; i++) {
      if (lst->Items[i]) {
        FreeMST_Object(lst->Items[i]);
      }
    }
    free(lst);
    return 0;
  } else if (obj->Type == MST_SVExpression) {
    MST_SVExpr* expr = (MST_SVExpr*)obj;
    if (expr->Prev) {
      delete expr->Prev;
    }
    if (expr->Ref) {
      delete expr->Ref;
    }
    free(expr);
    return 0;
  } else {
    cout << "error" << endl;
    exit(-1);
  }
}

MST_Object* CopyMST_Object(MST_Object* obj) {
  if (obj->Type == MST_Expression) {
    MST_Expr* src = (MST_Expr*)obj;
    MST_Expr* dst = AllocMST_Expr(src->nOperand);
    dst->Operator = src->Operator;
    for (int i = 0; i < src->nOperand; i++) {
      if (src->Operands[i]) {
        dst->Operands[i] = CopyMST_Object(src->Operands[i]);
      } else {
        dst->Operands[i] = NULL;
      }
    }
    return (MST_Object*)dst;
  } else if (obj->Type == MST_SVLogic || obj->Type == MST_Function || obj->Type == nMST_Task || obj->Type == MST_Symbol || obj->Type == MST_ExternalFunction) {
    return obj;
  } else if (obj->Type == MST_Value) {
    MST_Val* src = (MST_Val*)obj;
    int s = src->ItemWidth / 8;
    if (src->ItemWidth % 8) s++;
    for (int i = 0; i < src->nDim; i++) {
      s *= src->nItems[i];
    }
    s += sizeof(MST_Val) + src->nDim*4;
    MST_Val* dst = (MST_Val*)malloc(s);
    if (dst == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    memcpy(dst, src, s);
    dst->Object.Ptr = &dst->nItems[src->nDim];
    dst->ArrName = NULL;
    return (MST_Object*)dst;
  } else if (obj->Type == MST_SymbolReference) {
    MST_Object* dst = (MST_Object*)malloc(sizeof(MST_Object));
    if (dst == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    dst->Type = MST_SymbolReference;
    dst->Ptr = CopyMST_Object((MST_Object*)obj->Ptr);
    return dst;
  } else if (obj->Type == MST_String) {
    int size = 0;
    MST_Str* str = (MST_Str*)obj;
    while (str) {
      size += str->cLen;
      str = str->Next;
    }
    MST_Str* dst = (MST_Str*)malloc(sizeof(MST_Str)+size+1);
    if (dst == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    dst->Object.Type = MST_String;
    dst->Object.Ptr = dst;
    dst->mLen = size+1;
    dst->cLen = size;
    dst->Next = NULL;
    char* s = dst->Data;
    str = (MST_Str*)obj;
    while (str) {
      memcpy(s, str->Data, str->cLen);
      s += str->cLen;
      str = str->Next;
    }
    s[0] = 0;
    return (MST_Object*)dst;
  } else if (obj->Type == MST_List) {
    MST_Lst* src = (MST_Lst*)obj;
    MST_Lst* dst = AllocMST_Lst(src->nItems);
    for (int i = 0; i < src->nItems; i++) {
      if (src->Items[i]) {
        dst->Items[i] = CopyMST_Object(src->Items[i]);
      } else {
        dst->Items[i] = NULL;
      }
    }
    return (MST_Object*)dst;
  } else if (obj->Type == MST_ObjectReference) {
    MST_ObjRef* src = (MST_ObjRef*)obj;
    MST_ObjRef* dst = AllocMST_ObjRef(src->nIndex);
    dst->Object.Ptr = CopyMST_Object((MST_Object*)obj->Ptr);
    for (int i = 0; i < src->nIndex; i++) {
      dst->Index[i] = CopyMST_Object(src->Index[i]);
    }
    return (MST_Object*)dst;
  } else if (obj->Type == MST_SVExpression) {
    MST_SVExpr* src = (MST_SVExpr*)obj;
    MST_SVExpr* dst = (MST_SVExpr*)malloc(sizeof(MST_SVExpr));
    dst->Object.Type = MST_SVExpression;
    dst->Object.Ptr = NULL;
    string* prev = NULL;
    string* ref = NULL;
    if (src->Prev) {
      prev = new string;
      *prev = *(src->Prev);
    }
    if (src->Ref) {
      ref = new string;
      *ref = *(src->Ref);
    }
    dst->Prev = prev;
    dst->Ref = ref;
    return (MST_Object*)dst;
  } else {
    cout << "error" << endl;
    exit(-1);
  }
}

MST_Str* AllocMST_Str(int l) {
  MST_Str* str = (MST_Str*)malloc(sizeof(MST_Str)+l+1);
  str->Object.Type = MST_String;
  str->Object.Ptr = str;
  str->cLen = l;
  str->mLen = l+1;
  str->Data[0] = 0;
  str->Next = NULL;
  return str;
}

MST_Object* AllocMST_Val(int w) {
  int bw = w >> 3;
  if (w & 7) bw++;

  MST_Val* val = (MST_Val*)malloc(sizeof(MST_Val)+bw);
  if (val == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }

  val->Object.Ptr = &val->nItems[0];
  val->Object.Type = MST_Value;

  val->ArrName = NULL;
  val->ItemWidth = w;
  val->nDim = 0;

  return (MST_Object*)val;
}

MST_Object* AllocMST_Array(int w, vector<int> dim) {
  int bw = w >> 3;
  if (w & 7) bw++;
  int size = bw;
  for (int i = 0; i < dim.size(); i++) {
    size *= dim[i];
  }

  MST_Val* val = (MST_Val*)malloc(sizeof(MST_Val)+4*dim.size()+size);
  if (val == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }

  val->Object.Ptr = &val->nItems[dim.size()];
  val->Object.Type = MST_Value;

  val->ArrName = NULL;
  val->ItemWidth = w;
  val->nDim = dim.size();

  for (int i = 0; i < dim.size(); i++) {
    val->nItems[i] = dim[i];
  }

  return (MST_Object*)val;
}

int GetIntMST_Obj(MST_Object* obj) {
  int w;
  void* ptr;
  if (obj->Type == MST_Value) {
    MST_Val* val = (MST_Val*)obj;
    if (val->nDim || val->ItemWidth > 32) {
      cout << "error" << endl;
      exit(-1);
    }
    if (val->ItemWidth == 32) {
      return *(int*)(obj->Ptr);
    }
    uint8_t* ptr = (uint8_t*)obj->Ptr;
    int bw = val->ItemWidth >> 3;
    if (val->ItemWidth & 7) bw++;
    int n = 0;
    for (int i = 0; i < bw; i++) {
      n += ptr[i] << (i*8);
    }
    n &= (1 << val->ItemWidth)-1;
    return n;
  } else if (obj->Type == MST_SVLogic) {
    MST_SVLog* log = (MST_SVLog*)obj;
    if (log->nDim || log->ItemWidth > 32) {
      cout << "error" << endl;
      exit(-1);
    }
    int bw = log->ItemWidth >> 3;
    if (log->ItemWidth & 7) bw++;
    uint8_t* ptr;
    if (log->Closed) {
      ptr = (uint8_t*)log->Reg;
    } else {
      ptr = (uint8_t*)log->Wire;
    }
    int n = 0;
    for (int i = 0; i < bw; i++) {
      n += ptr[i] << (i*8);
    }
    if (log->ItemWidth == 32) {
      return n;
    }
    n &= (1 << log->ItemWidth)-1;
    return n;
  } else if (obj->Type == MST_ObjectReference) {
    MST_ObjRef* ref = (MST_ObjRef*)obj;
    MST_MemRef mref = MST_GetMemRef(ref);
    uint8_t* ptr = mref.ptr;
    if (mref.wid) {
      int n = ptr[0] >> mref.boff;
      int w = mref.wid + mref.boff - 8;
      int i = 0;
      while (0 < w) {
        ptr++;
        n += *ptr << (i * 8 + 8 - mref.boff);
        w -= 8;
        i++;
      }
      if (mref.wid == 32) return n;
      return n & ((1 << mref.wid)-1);
    } else {
      return 0;
    }
  } else if (obj->Type == MST_SymbolReference) {
    return GetIntMST_Obj(MST_GetSymVal(obj));
  } else if (obj->Type == MST_Expression) {
    MST_Object* val = EvalMST_Expr((MST_Expr*)obj, 1);
    if (!val) {
      cout << "error" << endl;
      exit(-1);
    }
    int n = GetIntMST_Obj(val);
    FreeMST_Object(val);
    return n;
  } else {
    cout << "error" << endl;
    exit(-1);
  }
  if (!ptr) {
    exit(-1);
  }
  int n = *((int*)ptr);
  n &= -1 >> (32 - w);
  return n;
}

MST_SVExpr SVCodeMST_Expr(MST_Expr* expr) {
  if (expr->Operator == MST_If) {
    return SVCodeMST_ExprIF(expr);
  } else if (expr->Operator == MST_Progn) {
    return SVCodeMST_ExprProgn(expr);
  } else if (expr->nOperand == 1) {
    return SVCodeMST_Expr1(expr);
  } else if (expr->nOperand == 2) {
    return SVCodeMST_Expr2(expr);
  } else {
    cout << "SVCodeMST_Expr: Invalid expression" << endl;
    exit(-1);
  }
}

MST_SVExpr SVCodeMST_ExprIF(MST_Expr* expr) {
  if (expr->nOperand < 2 || expr->nOperand > 3) {
    cout << "SVCodeMST_ExprIF: Invalid expression" << endl;
    exit(-1);
  }
  MST_SVExpr ret = {{NULL, MST_SVExpression}, NULL, NULL};
  MST_SVExpr cond = SVRefMST_Object(expr->Operands[0]);
  if (!cond.Ref) {
    cout << "SVCodeMST_ExprIF: Invalid expression" << endl;
    exit(-1);
  }
  string th;
  if (expr->Operands[1]->Type == MST_List) {
    MST_Lst* lst = (MST_Lst*)expr->Operands[1];
    for (int i = 0; i < lst->nItems; i++) {
      if (lst->Items[i]) {
        MST_SVExpr sv = SVRefMST_Object(lst->Items[i]);
        if (sv.Prev) {
          th += AddIndent(*sv.Prev);
          delete sv.Prev;
        }
        if (sv.Ref) delete sv.Ref;
      }
    }
  } else {
    MST_SVExpr sv = SVRefMST_Object(expr->Operands[0]);
    if (sv.Prev) {
      th = *sv.Prev;
      delete sv.Prev;
    }
    if (sv.Ref) delete sv.Ref;
  }
  string el;
  if (expr->nOperand == 3) {
    if (expr->Operands[2]->Type == MST_List) {
      MST_Lst* lst = (MST_Lst*)expr->Operands[2];
      for (int i = 0; i < lst->nItems; i++) {
        if (lst->Items[i]) {
          MST_SVExpr sv = SVRefMST_Object(lst->Items[i]);
          if (sv.Prev) {
            el += AddIndent(*sv.Prev);
            delete sv.Prev;
          }
          if (sv.Ref) delete sv.Ref;
        }
      }
    } else {
      MST_SVExpr sv = SVRefMST_Object(expr->Operands[0]);
      if (sv.Prev) {
        el = *sv.Prev;
        delete sv.Prev;
      }
      if (sv.Ref) delete sv.Ref;
    }
  }
  ret.Prev = cond.Prev;
  if (!ret.Prev) ret.Prev = new string;
  *ret.Prev += "if (" + *cond.Ref + ") begin\n" + th + "end";
  if (el.size()) {
    *ret.Prev += " else begin\n" + el + "end";
  }
  *ret.Prev += "\n";
  return ret;
}

MST_SVExpr SVCodeMST_ExprProgn(MST_Expr* expr) {
  MST_SVExpr ret = {{NULL, MST_SVExpression}, NULL, NULL};
  for (int i = 0; i < expr->nOperand; i++) {
    if (expr->Operands[i] && expr->Operands[i]->Type == MST_Expression) {
      MST_SVExpr sv = SVRefMST_Object(expr->Operands[i]);
      if (sv.Ref) delete sv.Ref;
      if (sv.Prev) {
        if (ret.Prev) {
          *(ret.Prev) += *(sv.Prev);
          delete sv.Prev;
        } else {
          ret.Prev = sv.Prev;
        }
      }
    }
  }
  return ret;
}

MST_SVExpr SVCodeMST_Expr1(MST_Expr* expr) {
  if (expr->nOperand != 1) {
    cout << "SVCodeMST_Expr: Invalid expression" << endl;
    exit(-1);
  }
  MST_SVExpr ret = SVRefMST_Object(expr->Operands[0]);
  if (!ret.Ref) {
    cout << "SVCodeMST_Expr: Invalid expression" << endl;
    exit(-1);
  }
  switch (expr->Operator) {
    case MST_BNot:
      *(ret.Ref) = "(~" + *(ret.Ref) + ")";
      break;
    case MST_LNot:
      *(ret.Ref) = "(!" + *(ret.Ref) + ")";
      break;
    default:
      cout << "SVCodeMST_Expr: Invalid expression" << endl;
      exit(-1);
  }
  return ret;
}

MST_SVExpr SVCodeMST_Expr2(MST_Expr* expr) {
  if (expr->nOperand != 2) {
    cout << "SVCodeMST_Expr: Invalid expression" << endl;
    exit(-1);
  }
  MST_SVExpr ret = SVRefMST_Object(expr->Operands[0]), oprd2 = SVRefMST_Object(expr->Operands[1]);
  if (!ret.Ref || !oprd2.Ref) {
    cout << "SVCodeMST_Expr: Invalid expression" << endl;
    exit(-1);
  }
  if (oprd2.Prev) {
    if (ret.Prev) {
      *(ret.Prev) += *(ret.Prev);
      delete oprd2.Prev;
    } else {
      ret.Prev = oprd2.Prev;
    }
  }
  switch (expr->Operator) {
    case MST_Set:
      if (!ret.Prev) ret.Prev = new string;
      *(ret.Prev) += *(ret.Ref) + " = " + *(oprd2.Ref) + ";\n";
      break;
    case MST_Add:
      *(ret.Ref) =  "(" + *(ret.Ref) + " + " + *(oprd2.Ref) + ")";
      break;
    case MST_Mul:
      *(ret.Ref) =  "(" + *(ret.Ref) + " * " + *(oprd2.Ref) + ")";
      break;
    case MST_Div:
      *(ret.Ref) =  "(" + *(ret.Ref) + " / " + *(oprd2.Ref) + ")";
      break;
    case MST_Pow:
      *(ret.Ref) =  "(" + *(ret.Ref) + " ** " + *(oprd2.Ref) + ")";
      break;
    case MST_BAnd:
      *(ret.Ref) =  "(" + *(ret.Ref) + " & " + *(oprd2.Ref) + ")";
      break;
    case MST_BOr:
      *(ret.Ref) =  "(" + *(ret.Ref) + " | " + *(oprd2.Ref) + ")";
      break;
    case MST_Xor:
      *(ret.Ref) =  "(" + *(ret.Ref) + " ^ " + *(oprd2.Ref) + ")";
      break;
    case MST_LAnd:
      *(ret.Ref) =  "(" + *(ret.Ref) + " && " + *(oprd2.Ref) + ")";
      break;
    case MST_LOr:
      *(ret.Ref) =  "(" + *(ret.Ref) + " || " + *(oprd2.Ref) + ")";
      break;
    case MST_Equal:
      *(ret.Ref) =  "(" + *(ret.Ref) + " == " + *(oprd2.Ref) + ")";
      break;
    case MST_Greater:
      *(ret.Ref) =  "(" + *(ret.Ref) + " > " + *(oprd2.Ref) + ")";
      break;
    case MST_GE:
      *(ret.Ref) =  "(" + *(ret.Ref) + " >= " + *(oprd2.Ref) + ")";
      break;
    case MST_Lesser:
      *(ret.Ref) =  "(" + *(ret.Ref) + " < " + *(oprd2.Ref) + ")";
      break;
    case MST_LE:
      *(ret.Ref) =  "(" + *(ret.Ref) + " <= " + *(oprd2.Ref) + ")";
      break;
    case MST_ShiftL:
      *(ret.Ref) =  "(" + *(ret.Ref) + " << " + *(oprd2.Ref) + ")";
      break;
    case MST_ShiftR:
      *(ret.Ref) =  "(" + *(ret.Ref) + " >> " + *(oprd2.Ref) + ")";
      break;
    default:
      cout << "SVCodeMST_Expr: Invalid expression" << endl;
      exit(-1);
  }
  delete oprd2.Ref;
  return ret;
}

MST_Expr* AllocMST_Expr(int n) {
  MST_Expr* expr = (MST_Expr*)malloc(sizeof(MST_Expr)+4*n);
  if (expr == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  expr->Object.Ptr = expr;
  expr->Object.Type = MST_Expression;
  expr->nOperand = n;
  return expr;
}

MST_Object* MST_Expr2(enum MST_Operator oprt, MST_Object* oprd1, MST_Object* oprd2) {
  MST_Expr* expr = (MST_Expr*)malloc(sizeof(MST_Expr)+8);
  if (expr == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }

  expr->Operator = oprt;
  expr->nOperand = 2;
  expr->Operands[0] = oprd1;
  expr->Operands[1] = oprd2;

  expr->Object.Ptr = expr;
  expr->Object.Type = MST_Expression;

  return (MST_Object*)expr;
}

MST_Object* EvalMST_Expr(MST_Expr* expr, int sim) {
  if (expr->Operator == MST_AddTrgTask) {
    if (expr->nOperand < 1 || expr->Operands[0]->Type != MST_List) {
      cout << "error" << endl;
      exit(-1);
    }
    MST_TrgTask* trg = AddTrgTask(expr->nOperand-1);
    MST_Lst* trglst = (MST_Lst*)expr->Operands[0];
    for (int i = 0; i < trglst->nItems; i++) {
      if (trglst->Items[i]->Type != MST_List) {
        cout << "error " << endl;
        exit(-1);
      }
      MST_Lst* t = (MST_Lst*)trglst->Items[i];
      if (t->nItems != 2) {
        cout << "error" << endl;
        exit(-1);
      }
      AddTrgMST_TrgTask(trg, (enum MST_Edge)GetIntMST_Obj(t->Items[0]), t->Items[1]);
    }
    for (int i = 1; i < expr->nOperand; i++) {
      trg->Expr[i-1] = (MST_Expr*)SolveMST_Object(CopyMST_Object(expr->Operands[i]), 1);
    }
    trg->nExpr = expr->nOperand-1;
    return NULL;
  } else if (expr->Operator == MST_NewFunc) {
    if (expr->nOperand < 2) {
      cout << "error" << endl;
      exit(-1);
    }
    if (expr->Operands[0]->Type != MST_SymbolReference || expr->Operands[1]->Type != MST_List) {
      cout << "error" << endl;
      exit(-1);
    }
    MST_Lst* arg = (MST_Lst*)expr->Operands[1];
    MST_Func* func = AddMST_Function(expr->Operands[0], arg->nItems, expr->nOperand-2);
    for (int i = 0; i < expr->nOperand-2; i++) {
      func->Expr[i] = (MST_Expr*)CopyMST_Object(expr->Operands[i+2]);
    }
    MST_TransArglst(func->Args, (MST_Lst*)expr->Operands[1]);
    return (MST_Object*)func;
  } else if (expr->Operator == MST_NewTask) {
    if (expr->nOperand < 2) {
      cout << "error" << endl;
      exit(-1);
    }
    if (expr->Operands[0]->Type != MST_SymbolReference || expr->Operands[1]->Type != MST_List) {
      cout << "error" << endl;
      exit(-1);
    }
    MST_Lst* arg = (MST_Lst*)expr->Operands[1];
    MST_Task* task = AddMST_Task(expr->Operands[0], arg->nItems, expr->nOperand-2);
    for (int i = 0; i < expr->nOperand-2; i++) {
      task->Expr[i] = (MST_Expr*)CopyMST_Object(expr->Operands[i+2]);
    }
    MST_TransArglst(task->Args, arg);
    return (MST_Object*)task;
  } else if (expr->Operator == MST_If) {
    if (expr->nOperand < 2 || expr->nOperand > 3) {
      cout << "error" << endl;
      exit(-1);
    }
    int f = 0;
    MST_Object* cond = expr->Operands[0];
    if (cond->Type == MST_Expression) {
      cond = EvalMST_Expr((MST_Expr*)cond, sim);
      f = 1;
    } else if (cond->Type == MST_Symbol == cond->Type == MST_SymbolReference) {
      cond = MST_GetSymVal(cond);
      f = 1;
    }
    int c = GetIntMST_Obj(cond);
    if (f) FreeMST_Object(cond);
    if (c) {
      if (expr->Operands[1]->Type == MST_Expression) {
        return EvalMST_Expr((MST_Expr*)expr->Operands[1], sim);
      } else if (expr->Operands[1]->Type == MST_List) {
        MST_Lst* lst = (MST_Lst*)expr->Operands[1];
        MST_Object* ret = NULL;
        for (int i = 0; i < lst->nItems; i++) {
          if (ret) FreeMST_Object(ret);
          ret = NULL;
          if (lst->Items[i] && lst->Items[i]->Type == MST_Expression)
            ret = EvalMST_Expr((MST_Expr*)lst->Items[i], sim);
        }
        return ret;
      } else {
        cout << "error" << endl;
        exit(-1);
      }
    } else {
      if (expr->Operands[2]->Type == MST_Expression) {
        return EvalMST_Expr((MST_Expr*)expr->Operands[2], sim);
      } else if (expr->Operands[2]->Type == MST_List) {
        MST_Lst* lst =(MST_Lst*) expr->Operands[2];
        MST_Object* ret = NULL;
        for (int i = 0; i < lst->nItems; i++) {
          if (ret) FreeMST_Object(ret);
          ret = NULL;
          if (lst->Items[i] && lst->Items[i]->Type == MST_Expression)
            ret = EvalMST_Expr((MST_Expr*)lst->Items[i], sim);
        }
        return ret;
      } else {
        cout << "error" << endl;
        exit(-1);
      }
    }
  } else if (expr->Operator == MST_Progn) {
    MST_Object* ret = NULL;
    for (int i = 0; i < expr->nOperand; i++) {
      if (ret) FreeMST_Object(ret);
      ret = NULL;
      if (expr->Operands[i] && expr->Operands[i]->Type == MST_Expression)
        ret = EvalMST_Expr((MST_Expr*)expr->Operands[i], sim);
    }
    return ret;
  } else if (expr->Operator == MST_For) {
    if (expr->nOperand < 2) {
      cout << "error" << endl;
      exit(-1);
    }
    if (expr->Operands[0]->Type != MST_SymbolReference) {
      cout << "error" << endl;
      exit(-1);
    }
    if (expr->Operands[1]->Type != MST_Value) {
      cout << "error" << endl;
      exit(-1);
    }
    int n = GetIntMST_Obj(expr->Operands[1]);
    MST_Object* val = AllocMST_Val(32);
    *((int*)val->Ptr) = 0;
    MST_Sym* cnt = MST_AddSpecialSym(expr->Operands[0], val);
    MST_Object* ret = NULL;
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < expr->nOperand - 2; j++) {
        if (ret) FreeMST_Object(ret);
        ret = NULL;
        if (expr->Operands[j+2] && expr->Operands[j+2]->Type == MST_Expression)
          ret = EvalMST_Expr((MST_Expr*)expr->Operands[j+2], sim);
      }
      *((int*)val->Ptr) = i+1;
      MST_BindSym((MST_Object*)cnt, val);
    }
    MST_DelSpecialSym();
    FreeMST_Object(val);
    return ret;
  }

  MST_Object** nobj = (MST_Object**)malloc(sizeof(MST_Object*) * expr->nOperand);
  MST_Object** oprd = (MST_Object**)malloc(sizeof(MST_Object*) * expr->nOperand);
  if (nobj == NULL || oprd == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  for (int i = 0; i < expr->nOperand; i++) {
    if (expr->Operands[i]->Type == MST_Expression) {
      nobj[i] = EvalMST_Expr((MST_Expr*)expr->Operands[i], sim);
      oprd[i] = nobj[i];
    } else if ((expr->Operands[i]->Type == MST_SymbolReference || expr->Operands[i]->Type == MST_Symbol)
                && !(expr->Operator == MST_Bind && i == 0)) {
      nobj[i] = MST_GetSymVal(expr->Operands[i]);
      oprd[i] = nobj[i];
    } else if (expr->Operands[i]->Type == MST_ObjectReference) {
      nobj[i] = SolveMST_Object(CopyMST_Object(expr->Operands[i]), 0);
      oprd[i] = nobj[i];
    } else {
      nobj[i] = NULL;
      oprd[i] = expr->Operands[i];
    }
  }
  MST_Object* ret = NULL;
  if (expr->Operator == MST_NewObj) {
    MST_SVLog* log = MST_AddObject(expr->nOperand ? expr->nOperand-1 : 0);
    int w = expr->nOperand ? GetIntMST_Obj(oprd[0]) : 1;
    log->ItemWidth = w;
    int size = w >> 3;
    if (size & 7) size++;
    for (int i = 1; i < expr->nOperand; i++) {
      int n = GetIntMST_Obj(oprd[i]);
      log->nItems[i-1] = n;
      size *= n;
    }
    void* ptr = malloc(size);
    if (ptr == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    log->Wire = ptr;
    memset(ptr, 0, size);

    ptr = malloc(size);
    if (ptr == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    log->Reg = ptr;
    memset(ptr, 0, size);
    ret = (MST_Object*)log;
  } else if (expr->Operator == MST_Bind) {
    MST_BindSym(oprd[0], oprd[1]);
    if (nobj[0]) {
      ret = nobj[0];
      nobj[0] = NULL;
    } else {
      ret = CopyMST_Object(oprd[0]);
    }
  } else if (expr->Operator == MST_NewPort) {
    if (expr->nOperand < 1) {
      cout << "error" << endl;
      exit(-1);
    }
    MST_SVLog* log = MST_AddObject(expr->nOperand > 1 ? expr->nOperand-2 : 0);

    int w = expr->nOperand > 1 ? GetIntMST_Obj(oprd[1]) : 1;
    log->IO = (enum MST_IOType)GetIntMST_Obj(oprd[0]);
    log->ItemWidth = w;
    int size = w >> 3;
    if (w & 7) size++;
    for (int i = 2; i < expr->nOperand; i++) {
      int n = GetIntMST_Obj(oprd[i]);
      log->nItems[i-2] = n;
      size *= n;
    }
    void* ptr = malloc(size);
    if (ptr == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    log->Wire = ptr;
    memset(ptr, 0, size);

    ptr = malloc(size);
    if (ptr == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    log->Reg = ptr;
    memset(ptr, 0, size);
    ret = (MST_Object*)log;
  } else if (expr->Operator == MST_Call) {
    if (expr->nOperand < 1) {
      cout << "error" << endl;
      exit(-1);
    }
    if (oprd[0]->Type == MST_Function) {
      ret = CallMST_Func((MST_Func*)oprd[0], expr->nOperand-1, oprd+1);
    } else if (oprd[0]->Type == nMST_Task) {
      cout << "error" << endl;
      exit(-1);
    } else if (oprd[0]->Type == MST_ExternalFunction) {
      MST_ExFunc* func = (MST_ExFunc*)oprd[0];
      ret = func->pFunc(expr->nOperand-1, oprd+1);
    } else {
      cout << "error" << endl;
      exit(-1);
    }
  } else if (expr->Operator == MST_GetInt) {
    if (expr->nOperand != 1) {
      cout << "error" << endl;
      exit(-1);
    }
    ret = AllocMST_Val(32);
    int* ptr = (int*)ret->Ptr;
    *ptr = GetIntMST_Obj(oprd[0]);
  } else if (expr->nOperand == 2) {
    int n = GetIntMST_Obj(oprd[1]);
    if (expr->Operator == MST_Set) {
      n = MST_SetInt(oprd[0], n);
      ret = AllocMST_Val(32);
      int* ptr = (int*)ret->Ptr;
      *ptr = n;
    } else {
      if ((expr->Operands[0]->Type == MST_Value && expr->Operands[1]->Type == MST_Value) || sim) {
        int op1 = GetIntMST_Obj(oprd[0]), op2 = GetIntMST_Obj(oprd[1]);
        ret = AllocMST_Val(32);
        int* ptr = (int*)ret->Ptr;
        *ptr = MSTOprt_2Arg(expr->Operator, op1, op2);
      } else {
        MST_Expr* ex = AllocMST_Expr(2);
        ex->Operator = expr->Operator;
        if (nobj[0]) {
          ex->Operands[0] = nobj[0];
          nobj[0] = NULL;
        } else {
          ex->Operands[0] = CopyMST_Object(oprd[0]);
        }
        if (nobj[1]) {
          ex->Operands[1] = nobj[1];
          nobj[1] = NULL;
        } else {
          ex->Operands[1] = CopyMST_Object(oprd[1]);
        }
        ret = (MST_Object*)ex;
      }
    }
  } else if (expr->nOperand == 1) {
    if (expr->Operands[0]->Type == MST_Value || sim) {
      int op1 = GetIntMST_Obj(oprd[0]);
      ret = AllocMST_Val(32);
      int* ptr = (int*)ret->Ptr;
      *ptr = MSTOprt_1Arg(expr->Operator, op1);
    } else if (expr->Operator == MST_BNot || expr->Operator == MST_LNot) {
      MST_Expr* ex = AllocMST_Expr(1);
      ex->Operator = expr->Operator;
      if (nobj[0]) {
        ex->Operands[0] = nobj[0];
        nobj[0] = NULL;
      } else {
        ex->Operands[0] = CopyMST_Object(oprd[0]);
      }
      ret = (MST_Object*)ex;
    } else {
      cout << "EvalMST_Expr: Invalid expression" << endl;
      exit(-1);
    }
  } else {
    cout << "EvalMST_Expr: Invalid expression" << endl;
    exit(-1);
  }
  for (int i = 0; i < expr->nOperand; i++) {
    if (nobj[i]) {
      FreeMST_Object(nobj[i]);
    }
  }
  free(nobj);
  free(oprd);
  return ret;
}

 MST_MemRef MST_GetMemRef(MST_ObjRef* ref) {
  vector<int> index = {};
  MST_Object* obj = NULL;
  while (ref) {
    for (int i = 0; i < ref->nIndex; i++) {
      index.push_back(GetIntMST_Obj(ref->Index[i]));
    }
    obj = (MST_Object*)ref->Object.Ptr;
    if (obj->Type == MST_ObjectReference) {
      ref = (MST_ObjRef*)obj;
    } else {
      break;
    }
  }
  uint8_t* ptr = NULL;
  int iw;
  int ndim;
  int* nitems;
  if (obj->Type == MST_SVLogic) {
    MST_SVLog* log = (MST_SVLog*)obj;
    iw = log->ItemWidth;
    ndim = log->nDim;
    nitems = log->nItems;
    ptr = log->Closed ? (uint8_t*)log->Reg : (uint8_t*)log->Wire;
  } else if (obj->Type == MST_Value) {
    MST_Val* val = (MST_Val*)obj;
    iw = val->ItemWidth;
    ndim = val->nDim;
    nitems = val->nItems;
    ptr = (uint8_t*)val->Object.Ptr;
  } else {
    cout << "invalid index" << endl;
    exit(-1);
  }
  int b = (index.size() == ndim+1);
  if (b && index[0] >= iw) {
    cout << "invalid index" << endl;
    exit(-1);
  }
  int s = iw >> 3;
  if (iw & 7) s++;
  int size = s;
  int off = 0;
  for (int i = 0; i < ndim; i++) {
    cout << ndim-i-b-1  << endl;
    if (nitems[i] <= index[ndim-i-b-1]) {
      cout << "index exceeds the size" << endl;
      exit(-1);
    }
    off += size * index[ndim-i-b-1];
    size *= nitems[i];
  }
  ptr += off;
  if (b) ptr += index[0] >> 3;
  return {obj, ptr, b ? index[0] & 7 : 0, b ? 1 : iw};
}

int MST_SetInt(MST_Object* obj, int n) {
  if (obj->Type == MST_SVLogic) {
    MST_SVLog* log = (MST_SVLog*)obj;
    if (log->nDim || log->ItemWidth > 32) {
      cout << "error" << endl;
      exit(-1);
    }
    MST_NotifyChange(log);
    if (log->ItemWidth == 32) {
      int* ptr = (int*)log->Wire;
      if (!ptr) {
        cout << "error" << endl;
        exit(-1);
      }
      *ptr = n;
      return n;
    }
    if (log->ItemWidth < 32)
      n &= (1 << log->ItemWidth)-1;
    int bw = log->ItemWidth >> 3;
    if (log->ItemWidth & 7) bw++;
    uint8_t* ptr = (uint8_t*)log->Wire;
    if (!ptr) {
      cout << "error" << endl;
      exit(-1);
    }
    for (int i = 0; i < bw; i++) {
      ptr[i] = n >> (i*8);
    }
    return n;
  } else if (obj->Type == MST_ObjectReference) {
    MST_ObjRef* ref = (MST_ObjRef*)obj;
    MST_MemRef mref = MST_GetMemRef(ref);
    if (mref.obj->Type == MST_SVLogic) {
      MST_SVLog* log = (MST_SVLog*)mref.obj;
      MST_NotifyChange(log);
      if (mref.wid < 32)
        n &= (1 << mref.wid) - 1;
      uint8_t* ptr = (uint8_t*)mref.ptr;
      if (mref.wid) {
        int w = mref.wid + mref.boff;
        int i = 1;
        int off = mref.boff;
        uint8_t t = 0;
        if (mref.boff) {
          t = ptr[0] & ((1 << mref.boff)-1);
        }
        if (w < 8) {
          ptr[0] =  t | (n << mref.boff) | (ptr[0] & (-1 << (mref.wid + mref.boff)));
          return n;
        } else {
          ptr[0] = t | (n << mref.boff);
        }
        while (0 < w) {
          if (w < 8) {
            ptr[i] = (n >> (i * 8 - mref.boff)) | (ptr[i] & (-1 << (8 - w)));
          } else {
            ptr[i] = n >> (i * 8 - mref.boff);
          }
          i++;
        }
        return n;
      } else {
        cout << "error" << endl;
        exit(-1);
      }
    } else {
      cout << "error" << endl;
      exit(-1);
    }
  } else {
    cout << "error" << endl;
    exit(-1);
  }
}

int MSTOprt_1Arg(enum MST_Operator oprt, int oprd) {
  switch (oprt) {
    case MST_BNot:
      return ~oprd;
    case MST_LNot:
      return !oprd;
    default:
      cout << "Invalid expression" << endl;
      exit(-1);
  }
}

int MSTOprt_2Arg(enum MST_Operator oprt, int oprd1, int oprd2) {
  switch (oprt) {
    case (MST_Add):
      return oprd1 + oprd2;
    case (MST_Sub):
      return oprd1 - oprd2;
    case (MST_Mul):
      return oprd1 * oprd2;
    case (MST_Div):
      return oprd1 / oprd2;
    case (MST_Pow):
      return pow(oprd1, oprd2);
    case (MST_BAnd):
      return oprd1 & oprd2;
    case (MST_BOr):
      return oprd1 | oprd2;
    case (MST_Xor):
      return oprd1 ^ oprd2;
    case (MST_LAnd):
      return oprd1 && oprd2;
    case (MST_LOr):
      return oprd1 || oprd2;
    case (MST_Equal):
      return oprd1 == oprd2;
    case (MST_Greater):
      return oprd1 > oprd2;
    case (MST_GE):
      return oprd1 >= oprd2;
    case (MST_Lesser):
      return oprd1 < oprd2;
    case (MST_LE):
      return oprd1 <= oprd2;
    case (MST_ShiftL):
      return oprd1 << oprd2;
    case (MST_ShiftR):
      return oprd1 >> oprd2;
    default:
      cout << "Invalid expression" << endl;
      exit(-1);
  }
}

MST_ObjRef* AllocMST_ObjRef(int n) {
  MST_ObjRef* ref = (MST_ObjRef*)malloc(sizeof(MST_ObjRef)+4*n);
  if (ref == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  ref->Object.Type = MST_ObjectReference;
  ref->nIndex = n;
  return ref;
}

MST_Lst* AllocMST_Lst(int n) {
  MST_Lst* lst = (MST_Lst*)malloc(sizeof(MST_Lst)+4*n);
  if (lst == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  lst->Object.Type = MST_List;
  lst->Object.Ptr = lst;
  lst->nItems = n;
  return lst;
}

MST_Func* AllocMST_Func(int nargs, int nexpr) {
  MST_Func* func = (MST_Func*)malloc(sizeof(MST_Func)+4*nexpr);
  if (func == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  func->Object.Type = MST_Function;
  func->Object.Ptr = func;
  func->Args = AllocMST_Lst(nargs*2);
  func->nExpr = nexpr;
  func->Name = NULL;
  return func;
}

int MST_TransArglst(MST_Lst* dst, MST_Lst* src) {
  for (int i = 0; i < src->nItems; i++) {
    if (src->Items[i]->Type == MST_SymbolReference) {
      dst->Items[i*2] =  CopyMST_Object(src->Items[i]);
      dst->Items[i*2+1] = NULL;
    } else if (src->Items[i]->Type == MST_List) {
      MST_Lst* a = (MST_Lst*)src->Items[i];
      if (a->nItems == 0 || a->nItems > 2) {
        cout << "error" << endl;
        exit(-1);
      }
      if (a->Items[0]->Type == MST_SymbolReference) {
        dst->Items[i*2] = CopyMST_Object(a->Items[0]);
        dst->Items[i*2+1] = CopyMST_Object(a->Items[1]);
      } else {
        cout << "error" << endl;
        exit(-1);
      }
    }
  }
  return 0;
}

int MST_BindArgs(MST_Lst* arglst, int nargs, MST_Object** args) {
  if (nargs > arglst->nItems/2) {
    cout << "error" << endl;
    exit(-1);
  }
  MST_OpenScope();
  for (int i = 0; i < arglst->nItems/2; i++) {
    if (i >= nargs) {
      if (!arglst->Items[i*2+1]) {
        cout << "error" << endl;
        exit(-1);
      }
      MST_BindSym(arglst->Items[i*2], arglst->Items[i*2+1]);
    } else {
      MST_BindSym(arglst->Items[i*2], args[i]);
    }
  }
  return 0;
}

MST_Object* CallMST_Func(MST_Func* func, int nargs, MST_Object** args) {
  MST_BindArgs(func->Args, nargs, args);
  MST_Object* ret = NULL;
  for (int i = 0; i < func->nExpr; i++) {
    if (ret) {
      FreeMST_Object(ret);
      ret = NULL;
    }
    MST_Object* copy = CopyMST_Object((MST_Object*)func->Expr[i]);
    ret = EvalMST_Expr((MST_Expr*)copy, 0);
    FreeMST_Object(copy);
  }
  MST_CloseScope();
  return ret;
}

MST_Task* AllocMST_Task(int nargs, int nexpr) {
  MST_Task* task = (MST_Task*)malloc(sizeof(MST_Task)+4*nexpr);
  if (task == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  task->Object.Type = nMST_Task;
  task->Object.Ptr = task;
  task->Name = NULL;
  task->Args = AllocMST_Lst(nargs*2);
  task->nExpr = nexpr;
  return task;
}

MST_ExFunc* AllocMST_ExFunc() {
  MST_ExFunc* func = (MST_ExFunc*)malloc(sizeof(MST_ExFunc));
  if (func == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  func->Object.Type = MST_ExternalFunction;
  func->Object.Ptr = func;
  func->Name = NULL;
  func->pFunc = NULL;
  return func;
}

MST_Object* SolveMST_Task(MST_Task* task, int nargs, MST_Object** args) {
  MST_BindArgs(task->Args, nargs, args);
  MST_Expr* expr = AllocMST_Expr(task->nExpr);
  expr->Operator = MST_Progn;
  for (int i = 0; i < task->nExpr; i++) {
    expr->Operands[i] = SolveMST_Object(CopyMST_Object((MST_Object*)task->Expr[i]), 1);
  }
  MST_CloseScope();
  return (MST_Object*)expr;
}

MST_Trigger* AddTrgMST_TrgTask(MST_TrgTask* task, enum MST_Edge edge, MST_Object* log) {
  if (log->Type == MST_SVLogic) {
    return AddTrgMST_TrgTask(task, edge, (MST_SVLog*)log);
  } else if (log->Type == MST_SymbolReference || log->Type == MST_Symbol) {
    return AddTrgMST_TrgTask(task, edge, MST_GetSymVal(log));
  } else  {
    cout << "error on add trgtask" << endl;
    exit(-1);
  }
}

MST_Trigger* AddTrgMST_TrgTask(MST_TrgTask* task, enum MST_Edge edge, MST_SVLog* log) {
  MST_Trigger* trg;
  if (task->Trg) {
    trg = task->Trg;
    while (trg->LinkByTask) trg = trg->LinkByTask;
    trg = (trg->LinkByTask = (MST_Trigger*)malloc(sizeof(MST_Trigger)));
    if (trg == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
  } else {
    trg = (MST_Trigger*)malloc(sizeof(MST_Trigger));
    if (trg == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    task->Trg = trg;
  }
  trg->Edge = edge;
  trg->Log = log;
  trg->LinkByLog = NULL;
  trg->LinkByTask = NULL;
  trg->Task = task;

  if (log->Triggers) {
    MST_Trigger* trglog = log->Triggers;
    while (trglog->LinkByLog) trglog = trglog->LinkByLog;
    trglog->LinkByLog = trg;
  } else {
    log->Triggers = trg;
  }
  return trg;
}

int FreeMST_TrgTask(MST_TrgTask* task) {
  MST_Trigger* trg = task->Trg;
  while (trg) {
    MST_Trigger* trgprev = trg;
    trg = trg->LinkByTask;

    if (trgprev->LinkByLog) {
      memcpy(trgprev, trgprev->LinkByLog, sizeof(MST_Trigger));
      free(trgprev->LinkByLog);
    } else {
      free(trgprev);
    }
  }

  for (int i = 0; i < task->nExpr; i++) {
    FreeMST_Object((MST_Object*)task->Expr[i]);
  }

  free(task);
  return 0;
}

string SVCodeMST_TrgTask(MST_TrgTask* task) {
  string ret = "\talways @(";
  MST_Trigger* trg = task->Trg;
  while (trg) {
    if (trg->Edge == MST_posedge) {
      ret += "posedge ";
    } else if (trg->Edge == MST_negedge) {
      ret += "negedge ";
    }
    MST_SVExpr ref = SVRefMST_Object((MST_Object*)trg->Log);
    if (ref.Ref) {
      ret += *(ref.Ref);
    } else {
      cout << "error" << endl;
      exit(-1);
    }
    trg = trg->LinkByTask;
    if (trg) ret += "or ";
  }
  ret += ") begin\n";
  for (int i = 0; i < task->nExpr; i++) {
    if (task->Expr[i] && task->Expr[i]->Object.Type == MST_Expression) {
      MST_SVExpr expr = SVCodeMST_Expr((MST_Expr*)task->Expr[i]);
      if (expr.Prev) {
        ret += AddIndent(*(expr.Prev), 2);
        delete expr.Prev;
      }
      if (expr.Ref) {
        delete expr.Ref;
      }
    }
  }
  ret += "\tend\n";
  return ret;
}

int EvalMST_TrgTask(MST_TrgTask* task) {
  for (int i = 0; i < task->nExpr; i++) {
    EvalMST_Expr((MST_Expr*)task->Expr[i], 1);
  }
  return 0;
}

MST_Env::MST_Env() {
  AddScope();
}

MST_Env::~MST_Env() {
  for (int i = 0; i < Objects.size(); i++) {
    for (int j = 0; j < Objects[i].size(); j++) {
      if (Objects[i][j]->Reg) free(Objects[i][j]->Reg);
      if (Objects[i][j]->Wire) free(Objects[i][j]->Wire);
      free(Objects[i][j]);
    }
  }
  for (int i = 0; i < TrgTasks.size(); i++) {
    FreeMST_TrgTask(TrgTasks[i]);
  }
  for (int i = 0; i < Symbols.size(); i++) {
    for (int j = 0; j < Symbols[j].size(); j++) {
      FreeMST_Object(Symbols[i][j]->Val);
      FreeMST_Object((MST_Object*)Symbols[i][j]->Name);
    }
  }
  for (int i = 0; i < Tables.size(); i++) {
    delete Tables[i];
  }
  for (int i = 0; i < Functions.size(); i++) {
    FreeMST_Object((MST_Object*)Functions[i]->Name);
    FreeMST_Object((MST_Object*)Functions[i]->Args);
    for (int j = 0; j < Functions[i]->nExpr; j++) {
      FreeMST_Object((MST_Object*)Functions[i]->Expr[j]);
    }
    free(Functions[i]);
  }
}

int MST_Env::AddScope() {
  Objects.push_back({});
  Tables.push_back(new HashTable<MST_Sym*>);
  Symbols.push_back({});
  SpecialSym.push_back({});
  return 0;
}

int MST_Env::CloseScope() {
  delete Tables.back();
  Tables.pop_back();
  SpecialSym.pop_back();
  return 0;
}


MST_SVLog* MST_Env::AddObject(int ndim) {
  if (ndim < 0) {
    ndim = MST_DEF_DIM;
  }
  MST_SVLog* obj = (MST_SVLog*)malloc(sizeof(MST_SVLog) + sizeof(int) * ndim);
  if (obj == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  if (Tables.size() > 1) {
    Objects.back().push_back(obj);
    obj->nScope = Objects.size()-1;
  } else {
    Objects[0].push_back(obj);
    obj->nScope = 0;
  }
  obj->Object.Ptr = NULL;
  obj->Object.Type = MST_SVLogic;
  obj->IO = MST_Internal;
  obj->Name = NULL;
  obj->Triggers = NULL;
  obj->Changed = 0;
  obj->Closed = 0;
  obj->Reg = NULL;
  obj->Wire = NULL;
  obj->nDim = ndim;
  return obj;
}

MST_TrgTask* MST_Env::AddTrgTask(int n) {
  MST_TrgTask* task = (MST_TrgTask*)malloc(sizeof(MST_TrgTask) + n * sizeof(MST_Expr*));
  if (task == NULL) {
    cout << "alloc error" << endl;
    exit(-1);
  }
  TrgTasks.push_back(task);
  task->Trg = NULL;
  task->nExpr = 0;
  return task;
}

MST_Func* MST_Env::AddFunction(MST_Object* name, int nargs, int nexpr) {
  MST_Func* func = AllocMST_Func(nargs, nexpr);
  Functions.push_back(func);
  func->Name = (MST_Str*)CopyMST_Object(name);
  MST_BindSym(name, (MST_Object*)func);
  return func;
}

MST_Task* MST_Env::AddTask(MST_Object* name, int nargs, int nexpr) {
  MST_Task* task = AllocMST_Task(nargs, nexpr);
  Tasks.push_back(task);
  task->Name = (MST_Str*)CopyMST_Object(name);
  MST_BindSym(name, (MST_Object*)task);
  return task;
}

MST_ExFunc* MST_Env::AddExFunc(MST_Object* name, MST_Object* (*pfunc)(int nargs, MST_Object** args)) {
  MST_ExFunc* func = AllocMST_ExFunc();
  ExFunctions.push_back(func);
  func->Name = (MST_Str*)CopyMST_Object(name);
  func->pFunc = pfunc;
  MST_BindSym(name, (MST_Object*)func);
  return func;
}

MST_ExFunc* MST_Env::AddExFunc(char* name, MST_Object* (*pfunc)(int nargs, MST_Object** args)) {
  MST_ExFunc* func = AllocMST_ExFunc();
  ExFunctions.push_back(func);
  func->Name = AllocMST_Str(strlen(name));
  func->pFunc = pfunc;
  strcpy(func->Name->Data, name);
  MST_BindSym((MST_Object*)func->Name, (MST_Object*)func);
  return func;
}

MST_ExFunc* MST_Env::AddExFunc(string name, MST_Object* (*pfunc)(int nargs, MST_Object** args)) {
  MST_ExFunc* func = AllocMST_ExFunc();
  ExFunctions.push_back(func);
  func->Name = AllocMST_Str(name.size());
  func->pFunc = pfunc;
  strcpy(func->Name->Data, name.c_str());
  MST_BindSym((MST_Object*)func->Name, (MST_Object*)func);
  return func;
}

int MST_Env::AllocObjects() {
  for (int i = 0; i < Objects.size(); i++) {
    for (int j = 0; j < Objects[i].size(); j++) {
      if (Objects[i][j]->Wire == NULL) {
        int size;
        size = Objects[i][j]->ItemWidth / 8;
        if (Objects[i][j]->ItemWidth % 8) size++;
        for (int k = 0; k < Objects[i][j]->nDim; k++) {
          size *= Objects[i][j]->nItems[k];
        }
        void* ptr = malloc(size);
        if (ptr == NULL) {
          cout << "alloc error" << endl;
          exit(-1);
        }
        Objects[i][j]->Wire = ptr;
        memset(ptr, 0, size);

        ptr = malloc(size);
        if (ptr == NULL) {
          cout << "alloc error" << endl;
          exit(-1);
        }
        Objects[i][j]->Reg = ptr;
        memset(ptr, 0, size);
      }
    }
  }
  return 0;
}

int MST_Env::NotifyChange(MST_SVLog* log) {
  if (log->Closed) {
    cout << "Changing a value of the closed object" << endl;
    return -1;
  }
  if (log->Changed) {
    return 0;
  }
  Changes.push_back(log);
  log->Changed = 1;
  return 0;
}

int MST_Env::WaitTask() {
  vector<MST_SVLog*> list = Changes;
  Changes = {};
  for (int i = 0; i < list.size(); i++) {
    list[i]->Closed = 0;
  }
  int n = 0;
  for (int i = 0; i < list.size(); i++) {
    list[i]->Changed = 0;
    MST_Trigger* trg = list[i]->Triggers;
    int size = list[i]->ItemWidth >> 3;
    if (list[i]->ItemWidth & 7) size++;
    for (int i = 0; i < list[i]->nDim; i++) {
      size *= list[i]->nItems[i];
    }
    if (trg) {
      int edge = 0; //pos: 1, neg: 2, none: 3
      int ch = 0;

      while (trg) {
        if ((trg->Edge == MST_posedge || trg->Edge == MST_negedge) && !edge) {
          int w = 0;
          for (int i = 0; i < size && !w; i++) {
            w |= ((uint8_t*)list[i]->Wire)[i];
          }
          int r = 0;
          for (int i = 0; i < size && !r; i++) {
            r |= ((uint8_t*)list[i]->Reg)[i];
          }
          if (!w == !r) {
            edge = 3;
          } else if (w && !r) {
            edge = 1;
            ch = 1;
          } else {
            edge = 2;
            ch = 1;
          }
        }
        if (trg->Edge == MST_atchange && !ch) {
          if (memcmp(list[i]->Wire, list[i]->Reg, size)) {
            ch = 1;
          } else {
            ch = 2;
            edge = 3;
          }
        }
        int c = 0;
        if (trg->Edge == MST_posedge) {
          if (edge == 1) {
            c = 1;
          }
        } else if (trg->Edge == MST_negedge) {
          if (edge == 2) {
            c = 1;
          }
        } else if (trg->Edge == MST_atchange) {
          if (ch == 1) {
            c = 1;
          }
        }
        if (c) {
          for (int i = 0; i < trg->Task->nExpr; i++) {
            EvalMST_Expr(trg->Task->Expr[i], 1);
          }
        }
        trg = trg->LinkByLog;
      }
    }
    memcpy(list[i]->Reg, list[i]->Wire, size);
    for (int i = n; i < Changes.size(); i++) {
      Changes[i]->Closed = 1;
    }
    n = Changes.size();
  }
  if (Changes.size()) {
    return WaitTask();
  }
  return 0;
}

int MST_Env::Bind(MST_Object* sym, MST_Object* obj) {
  if (sym->Type == MST_String) {
    MST_Str* str = (MST_Str*)sym;
    string name = "";
    while (str) {
      name += string(str->Data, str->cLen);
      str = str->Next;
    }
    MST_Sym* dst = NULL;
    for (int i = 0; i < SpecialSym.back().size(); i++) {
      string name2 = "";
      MST_Str* s = SpecialSym.back()[SpecialSym.back().size()-i-1]->Name;
      while (s) {
        name2 += string(s->Data, s->cLen);
        s = s->Next;
      }
      if (name2 == name) {
        dst = SpecialSym.back()[SpecialSym.back().size()-i-1];
        break;
      }
    }
    if (!dst) {
      MST_Sym** ss = Tables.back()->Find(name);
      if (ss) dst = *ss;
    }
    if (obj->Type == MST_SVLogic) {
      MST_SVLog* log = (MST_SVLog*)obj;
      if (!log->Name) {
        string svname = name;
        while (MST_FindSVName(svname)) {
          svname += "_";
        }
        MST_BindSVName(svname, obj);
        MST_Str* ssvname = AllocMST_Str(svname.size());
        strcpy(ssvname->Data, svname.c_str());
        log->Name = ssvname;
      }
    }
    if (dst) {
      FreeMST_Object(dst->Val);
      dst->Val = CopyMST_Object(obj);
    } else {
      MST_Sym* s = (MST_Sym*)malloc(sizeof(MST_Sym));
      if (s == NULL) {
        cout << "alloc error" << endl;
        exit(-1);
      }
      Symbols.back().push_back(s);
      Tables.back()->Get(name) = s;
      s->Name = (MST_Str*)CopyMST_Object(sym);
      s->Val = CopyMST_Object(obj);
      s->Object.Ptr = s;
      s->Object.Type = MST_Symbol;
    }
    return 0;
  } else if (sym->Type == MST_SymbolReference) {
    return Bind((MST_Object*)sym->Ptr, obj);
  } else if (sym->Type == MST_Symbol) {
    MST_Sym* s = (MST_Sym*)sym;
    s->Val = CopyMST_Object(obj);
    return 0;
  } else {
    cout << "error" << endl;
    exit(-1);
  }
}

MST_Sym* MST_Env::GetSym(MST_Object* sym) {
  if (sym->Type == MST_String) {
    MST_Str* str = (MST_Str*)sym;
    string name = "";
    while (str) {
      name += string(str->Data, str->cLen) ;
      str = str->Next;
    }
    for (int i = 0; i < SpecialSym.back().size(); i++) {
      string name2 = "";
      MST_Str* s = SpecialSym.back()[SpecialSym.back().size()-i-1]->Name;
      while (s) {
        name2 += string(s->Data, s->cLen);
        s = s->Next;
      }
      if (name2 == name) {
        return SpecialSym.back()[SpecialSym.back().size()-i-1];
      }
    }
    for (int i = 0; i < Tables.size(); i++) {
      MST_Sym** s = Tables[Tables.size()-i-1]->Find(name);
      if (s) {
        return *s;
      }
    }
    cout << "symbol not bound " << name << endl;
    exit(-1);
  } else if (sym->Type == MST_SymbolReference) {
    return GetSym((MST_Object*)sym->Ptr);
  } else if (sym->Type == MST_Symbol) {
    return (MST_Sym*)sym;
  }
  cout << "error" << endl;
  exit(-1);
}

MST_Object* MST_Env::GetSymVal(MST_Object* sym) {
  return GetSym(sym)->Val;
}

MST_Sym* MST_Env::AddSpecialSym(MST_Object* sym, MST_Object* val) {
  if (sym->Type == MST_String) {
    MST_Sym* s = (MST_Sym*)malloc(sizeof(MST_Sym));
    if (s == NULL) {
      cout << "alloc error" << endl;
      exit(-1);
    }
    Symbols.back().push_back(s);
    SpecialSym.back().push_back(s);
    s->Name = (MST_Str*)CopyMST_Object(sym);
    s->Val = CopyMST_Object(val);
    s->Object.Ptr = s;
    s->Object.Type = MST_Symbol;
    return s;
  } else if (sym->Type == MST_SymbolReference) {
    return AddSpecialSym((MST_Object*)sym->Ptr, val);
  } else {
    cout << "error" << endl;
    exit(-1);
  }
}

int MST_Env::DelSpecialSym() {
  if (!SpecialSym.back().size()) {
    cout << "error" << endl;
    exit(-1);
  }
  SpecialSym.back().pop_back();
  return 0;
}

int MST_Env::BindSVName(string name, MST_Object* obj) {
  if (SVNameTable.Find(name)) {
    return -1;
  } else {
    SVNameTable.Get(name) = obj;
    return 0;
  }
}

int MST_Env::FindSVName(string name) {
  if (SVNameTable.Find(name)) {
    return 1;
  } else {
    return 0;
  }
}

int MST_Env::AddArray(MST_Val* array) {
  if (array->ArrName) return 0;
  string* name = new string;
  srand(time(NULL));
  for (int i = 0; i < 255; i++) {
    *name = "array_";
    ostringstream ss;
    ss << setfill('0') << setw(4) << std::hex << (rand() & 0xffff);
    *name += ss.str();
    if (!FindSVName(*name)) {
      array->ArrName = name;
      BindSVName(*name, (MST_Object*)array);
      Arrays.push_back(array);
      return 0;
    }
  }
  cout << "error" << endl;
  exit(-1);
}

string MST_Env::SVCode() {
  string port;
  string interobj;
  for (int i = 0; i < Objects.size(); i++) {
    for (int j = 0; j < Objects[i].size(); j++) {
      if (Objects[i][j]->IO) {
        if (port.size()) port += ",\n";
        port = port + "\t" + SVDecMST_Object(Objects[i][j]);
      } else {
        interobj += "\t" + SVDecMST_Object(Objects[i][j]) + ";\n";
      }
    }
  }
  string log;
  for (int i = 0; i < TrgTasks.size(); i++) {
    log += SVCodeMST_TrgTask(TrgTasks[i]);
  }
  string arr;
  for (int i = 0; i < Arrays.size(); i++) {
    if (Arrays[i]->nDim > 1) {
      cout << "TO DO" << endl;
      exit(-1);
    }
    arr += "\tint " + *(Arrays[i]->ArrName) + "[" + to_string(Arrays[i]->nItems[0]) + "] = '{";
    int* ptr = (int*)Arrays[i]->Object.Ptr;
    for (int j = 0; j < Arrays[i]->nItems[0]; j++) {
      if (j) arr += ", ";
      arr += to_string(ptr[j]);
    }
    arr += "};\n";
  }
  string ret = "module MAIN (\n" + port + "\n);\n" + interobj;
  if (arr.size()) {
    ret += "\n" + arr;
  }
  if (log.size()) {
    ret += "\n" + log;
  }
  ret += "\nendmodule\n";
  return ret;
}

MST_SVLog* MST_AddObject(int ndim) {
  return mst_env->AddObject(ndim);
}

int MST_AllocObjects() {
  return mst_env->AllocObjects();
}

MST_TrgTask* AddTrgTask(int n) {
  return mst_env->AddTrgTask(n);
}

int MST_NotifyChange(MST_SVLog* log) {
  return mst_env->NotifyChange(log);
}

int MST_WaitTask() {
  return mst_env->WaitTask();
}

int MST_BindSym(MST_Object* sym, MST_Object* obj) {
  return mst_env->Bind(sym, obj);
}

MST_Sym* MST_GetSym(MST_Object* sym) {
  return mst_env->GetSym(sym);
}

MST_Object* MST_GetSymVal(MST_Object* sym) {
  return mst_env->GetSymVal(sym);
}

MST_Func* AddMST_Function(MST_Object* name, int nargs, int nexpr) {
  return mst_env->AddFunction(name, nargs, nexpr);
}

MST_Task* AddMST_Task(MST_Object* name, int nargs, int nexpr) {
  return mst_env->AddTask(name, nargs, nexpr);
}

MST_ExFunc* AddMST_ExFunc(MST_Object* name, MST_Object* (*pfunc)(int nargs, MST_Object** args)) {
  return mst_env->AddExFunc(name, pfunc);
}

MST_ExFunc* AddMST_ExFunc(char* name, MST_Object* (*pfunc)(int nargs, MST_Object** args)) {
  return mst_env->AddExFunc(name, pfunc);
}

MST_ExFunc* AddMST_ExFunc(string name, MST_Object* (*pfunc)(int nargs, MST_Object** args)) {
  return mst_env->AddExFunc(name, pfunc);
}

string MST_SVCode() {
  return mst_env->SVCode();
}

int MST_OpenScope() {
  return mst_env->AddScope();
}

int MST_CloseScope() {
  return mst_env->CloseScope();
}

MST_Sym* MST_AddSpecialSym(MST_Object* sym, MST_Object* val) {
  return mst_env->AddSpecialSym(sym, val);
}

int MST_DelSpecialSym() {
  return mst_env->DelSpecialSym();
}

int MST_BindSVName(string name, MST_Object* obj) {
  return mst_env->BindSVName(name, obj);
}

int MST_FindSVName(string name) {
  return mst_env->FindSVName(name);
}

int MST_AddArray(MST_Val* array) {
  return mst_env->AddArray(array);
}
