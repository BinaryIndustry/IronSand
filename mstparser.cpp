#include "mightstone.h"
#include "mstparser.h"
#include <string>
#include <vector>
#include <variant>
#include <conio.h>
#include <fstream>
#include "hashtable.cpp"

using namespace std;

static MST_Parser* mstp = new MST_Parser;

MST_Parser::MST_Parser() {
  static vector<string> oprt = {"=", "+", "-", "*", "/", "**", "&", "|", "^", "&&", "||", "~", "!", "==", "!=", ">", ">=", "<", "<=", "<<", ">>", "[", "]", "(", ")", " ", "\t", "\n", ":", ",", "0x", "$", "$=", "{", "}", "+:", "-:", ".", ";", "+=", "-=", "*=", "/=", "**=", "&=", "|=", "^=", "&&=", "||="};
  for (int i = 0; i < oprt.size(); i++) {
    MSTP_TokenInfo* info = new MSTP_TokenInfo;
    OprtTable.Get(oprt[i]) = info;
    Operators.push_back(info);
    info->OprtID = i;
    info->WordID = -1;
  }
  static vector<string> words = {"in", "out", "io", "at", "pos", "neg", "defun", "if", "else", "for", "deftask"};
  for (int i = 0; i < words.size(); i++) {
    MSTP_TokenInfo* info = new MSTP_TokenInfo;
    WordTable.Get(words[i]) = info;
    Words.push_back(info);
    info->OprtID = -1;
    info->WordID = i;
  }
  Mode = 1;
}

MST_Parser::~MST_Parser() {
  for (int i = 0; i < Operators.size(); i++) {
    free(Operators[i]);
  }
  for (int i = 0; i < Words.size(); i++) {
    free(Words[i]);
  }
}

int ErrorFlagMSTP = 0;

vector<MST_Object*> MST_Parser::Parse(char* src) {
  vector<MST_Object*> ret = {};
  int len = strlen(src);
  if (!len) return {};
  src[len++] = '\n';
  src[len++] = '\n';
  src[len] = 0;
  char* s = src;
  char* end = src + len;
  vector<MSTP_Token> tokens = {};
  while (src < end) {
    int i = OprtTable.SearchBack((uint8_t*)src, src - end);
    if (i) {
      if (s != src) {
        MSTP_TokenInfo** info = WordTable.Find((uint8_t*)s, src - s);
        tokens.push_back({info ? *info : NULL, s, src - s});
      }
      tokens.push_back({OprtTable.Get((uint8_t*)src, i), src, i});
      src += i;
      s = src;
    } else {
      src++;
    }
  }
  int i = 0;
  int atnest = 0;
  int defun = 0;
  int deftask = 0;

  vector<pair<int,MST_Object*>> triggers = {};
  vector<MST_Object*> trgtask = {};

  vector<MST_Expr*> funcexpr = {};
  vector<MST_Object*> funcargs = {};
  MST_Object* funcname = NULL;

  vector<int> ifnest = {};
  vector<vector<MST_Object*>> ifcond = {};
  vector<vector<vector<MST_Expr*>>> ifthen = {};

  vector<int> fornest = {};
  vector<MST_Object*> forcnt = {};
  vector<MST_Object*> formax = {};
  vector<vector<MST_Expr*>> forexpr = {};

  while (i < tokens.size()) {
    vector<int> line;
    int cnest = 0;
    int npar = 0, nbracket = 0, ncbracket = 0;
    while (i < tokens.size()) {
      if (tokens[i].Info) {
        int id = tokens[i].Info->OprtID;
        if (id == MSTP_Space) {
          if (line.size()) {
            i++;
            continue;
          }
          if (i+1 < tokens.size() && tokens[i+1].Info && tokens[i+1].Info->OprtID == MSTP_Space) {
            cnest++;
            i += 2;
          } else {
            i++;
          }
          continue;
        }
        if (id == MSTP_Tab) {
          if (line.size() == 0) {
            cnest++;
          }
          i++;
          continue;
        }
        if (id == MSTP_ParenL) {
          npar++;
        }
        if (id == MSTP_ParenR) {
          if (npar) npar--;
        }
        if (id == MSTP_BracketL) {
          nbracket++;
        }
        if (id == MSTP_BracketR) {
          if (nbracket) nbracket--;
        }
        if (id == MSTP_CurlyBracketL) {
          ncbracket++;
        }
        if (id == MSTP_CurlyBracketR) {
          if (ncbracket) ncbracket--;
        }
        if (id == MSTP_NL) {
          i++;
          if (!npar && !nbracket && !ncbracket) {
            break;
          }
          continue;
        }
      }
      line.push_back(i);
      i++;
    }
    if (!line.size() && i < tokens.size()) continue;
    vector<variant<MSTP_TokenInfo*, MST_Object*>> list = {};
    for (int j = 0; j < line.size(); j++) {
      int n = line[j];
      if (!tokens[n].Info) {
        uint8_t* ptr = (uint8_t*)tokens[n].Pos;
        if ('0' <= ptr[0] && ptr[0] <= '9') {
          MST_Object* val = AllocMST_Val(32);
          if (val == NULL) {
            cout << "allocation error" << endl;
            return {};
          }
          int* v = (int*)val->Ptr;
          *v = 0;
          for (int k = 0; k < tokens[n].Len; k++) {
            *v *= 10;
            if (!('0' <= ptr[k] && ptr[k] <= '9')) {
              cout << "parse error" << endl;
              return {};
            }
            *v += ptr[k] - '0';
          }
          list.push_back(val);
        } else {
          MST_Object* sym = (MST_Object*)malloc(sizeof(MST_Object));
          if (sym == NULL) {
            cout << "allocation error" << endl;
            return {};
          }
          MST_Str* str = AllocMST_Str(tokens[n].Len);
          if (str == NULL) {
            cout << "allocation error" << endl;
            return {};
          }
          sym->Type = MST_SymbolReference;
          sym->Ptr = str;

          memcpy(str->Data, tokens[n].Pos, tokens[n].Len);
          str->Data[tokens[n].Len] = 0;
          list.push_back(sym);
        }
      } else {
        int idop = tokens[n].Info->OprtID;
        if (idop == MSTP_Space || idop == MSTP_Tab) continue;
        list.push_back(tokens[n].Info);
      }
    }

    int fwid = -1;
    if (list.size() && list[0].index() == 0)
      fwid = get<MSTP_TokenInfo*>(list[0])->WordID;

    int lastnest = 0; //0: none, 1:at, 2: defun, 3:if, 4:for 5:deftask
    int secnest = 0;

    while (1) {
      int dep = 0;
      int secdep = 0;

      lastnest = 0;
      secnest = 0;

      if (defun) {
        lastnest = 2;
        dep = 1;
      }

      if (deftask) {
        if (lastnest) {
          secnest = lastnest;
          secdep = dep;
        }
        lastnest = 5;
        dep = 1;
      }

      if (atnest && atnest > dep) {
        if (lastnest) {
          secnest = lastnest;
          secdep = dep;
        }
        lastnest = 1;
        dep = atnest;
      } else if (atnest && atnest > secdep) {
        secnest = 1;
        secdep = atnest;
      }

      if (ifnest.size() && ifnest.back() > dep) {
        if (lastnest) {
          secnest = lastnest;
          secdep = dep;
        }
        lastnest = 3;
        dep = ifnest.back();
      } else if (ifnest.size() && ifnest.back() > secdep) {
        secnest = 3;
        secdep = ifnest.back();
      }

      if (ifnest.size() > 1 && ifnest[ifnest.size()-2] > secdep) {
        secnest = 3;
        secdep = ifnest[ifnest.size()-2];
      }

      if (fornest.size() && fornest.back() > dep) {
        if (lastnest) secnest = lastnest;
        lastnest = 4;
        dep = fornest.back();
      } else if (fornest.size() && fornest.back() > secdep) {
        secnest = 4;
        secdep = fornest.back();
      }

      if (fornest.size() > 1 && fornest[fornest.size()-2] > secdep) {
        secnest = 4;
        fornest[fornest.size()-2] = secdep;
      }

      if (ifnest.size() && ifnest.back() > cnest + (fwid == MSTP_Else) && lastnest == 3) {
        MST_Expr* expr = AllocMST_Expr(1 + ifthen.back().size());
        expr->Operator = MST_If;
        if (ifcond.back().size() == 1) {
          expr->Operands[0] = ifcond.back().back();
        } else {
          MST_Lst* clst = AllocMST_Lst(ifcond.back().size());
          for (int j = 0; j < ifcond.back().size(); j++) {
            clst->Items[j] = ifcond.back()[j];
          }
        }
        for (int j = 0; j < ifthen.back().size(); j++) {
          MST_Lst* t = AllocMST_Lst(ifthen.back()[j].size());
          expr->Operands[j+1] = (MST_Object*)t;
          for (int k = 0; k < ifthen.back()[j].size(); k++) {
            t->Items[k] = (MST_Object*)ifthen.back()[j][k];
          }
        }
        ifcond.pop_back();
        ifnest.pop_back();
        ifthen.pop_back();
        if (secnest == 1) {
          trgtask.push_back((MST_Object*)expr);
        } else if (secnest == 3) {
          ifthen.back().back().push_back(expr);
        } else if (secnest == 2 || secnest == 5) {
          funcexpr.push_back(expr);
        } else if (secnest == 4) {
          forexpr.back().push_back(expr);
        } else {
          ret.push_back((MST_Object*)expr);
        }
        continue;
      }

      if (fornest.size() && fornest.back() > cnest && lastnest == 4) {
        MST_Expr* expr = AllocMST_Expr(2+forexpr.back().size());
        expr->Operator = MST_For;
        expr->Operands[0] = forcnt.back();
        expr->Operands[1] = formax.back();
        for (int j = 0; j < forexpr.back().size(); j++) {
          expr->Operands[2+j] = (MST_Object*)forexpr.back()[j];
        }
        fornest.pop_back();
        forcnt.pop_back();
        formax.pop_back();
        forexpr.pop_back();
        if (secnest == 1) {
          trgtask.push_back((MST_Object*)expr);
        } else if (secnest == 3) {
          ifthen.back().back().push_back(expr);
        } else if (secnest == 2 || secnest == 5) {
          funcexpr.push_back(expr);
        } else if (secnest == 4) {
          forexpr.back().push_back(expr);
        } else {
          ret.push_back((MST_Object*)expr);
        }
        continue;
      }

      if (atnest && atnest > cnest && lastnest == 1) {
        atnest = 0;
        MST_Expr* expr = AllocMST_Expr(trgtask.size()+1);
        expr->Operator = MST_AddTrgTask;
        MST_Lst* trglist = AllocMST_Lst(triggers.size());
        for (int j = 0; j < triggers.size(); j++) {
          MST_Lst* trg = AllocMST_Lst(2);
          MST_Object* val = AllocMST_Val(32);
          if (triggers[j].first == MSTP_Pos) {
            *((int*)val->Ptr) = 1;
          } else if (triggers[j].first == MSTP_Neg) {
            *((int*)val->Ptr) = 2;
          } else {
            *((int*)val->Ptr) = 0;
          }
          trg->Items[0] = val;
          trg->Items[1] = triggers[j].second;
          trglist->Items[j] = (MST_Object*)trg;
        }
        expr->Operands[0] = (MST_Object*)trglist;
        for (int j = 0; j < trgtask.size(); j++) {
          expr->Operands[j+1] = trgtask[j];
        }
        if (secnest == 3) {
          ifthen.back().back().push_back(expr);
        } else if (secnest == 2 || secnest == 5) {
          funcexpr.push_back(expr);
        } else if (secnest == 4) {
          forexpr.back().push_back(expr);
        } else {
          ret.push_back((MST_Object*)expr);
        }
        trgtask = {};
        triggers = {};
        continue;
      }

      if (!cnest && (defun || deftask)) {
        MST_Expr* expr = AllocMST_Expr(funcexpr.size()+2);
        expr->Operator = defun ? MST_NewFunc : MST_NewTask;
        MST_Lst* arglst = AllocMST_Lst(funcargs.size());
        for (int j = 0; j < funcargs.size(); j++) {
          arglst->Items[j] = funcargs[j];
        }
        expr->Operands[0] = funcname;
        expr->Operands[1] = (MST_Object*)arglst;
        for (int j = 0; j < funcexpr.size(); j++) {
          expr->Operands[j+2] = (MST_Object*)funcexpr[j];
        }
        ret.push_back((MST_Object*)expr);
        funcexpr = {};
        funcargs = {};
        defun = 0;
        deftask = 0;
        continue;
      }

      break;
    }

    if (fwid == MSTP_At) {
      if (atnest || list.size() == 1) {
        cout << "parse error" << endl;
        return {};
      }
      atnest = cnest + 1;
      triggers = {};
      trgtask = {};
      int parl = 0;
      if (list[1].index() == 0 && get<MSTP_TokenInfo*>(list[1])->OprtID == MSTP_ParenL) {
        parl = 1;
      }
      int j;
      for (j = 1 + parl; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenR) {
            if (!parl) {
              cout << "parse error" << endl;
              return {};
            }
            break;
          } else if (idop == MSTP_Comma) {
            continue;
          }

          int idwd = get<MSTP_TokenInfo*>(list[j])->WordID;
          if (idwd == MSTP_Pos || idwd == MSTP_Neg) {
            if (j+1 >= list.size() || list[j+1].index() != 1) {
              cout << "parse error" << endl;
              return {};
            }
            triggers.push_back({idwd, get<MST_Object*>(list[j+1])});
            j++;
            continue;
          }
          cout << "parse error" << endl;
          return {};
        } else {
          triggers.push_back({-1, get<MST_Object*>(list[j])});
        }
      }
      continue;
    } else if (fwid == MSTP_Defun || fwid == MSTP_Deftask) {
      if (defun || atnest || deftask || ifnest.size()) {
        cout << "parse error" << endl;
        return {};
      }
      if (list.size() < 4) {
        cout << "parse error" << endl;
        return {};
      }
      if (fwid == MSTP_Defun) {
        defun = 1;
      } else {
        deftask = 1;
      }
      funcargs = {};
      funcexpr = {};
      if (list[1].index() != 1 || get<MST_Object*>(list[1])->Type != MST_SymbolReference) {
        cout << "parse error" << endl;
        return {};
      }
      funcname = get<MST_Object*>(list[1]);
      if (list[2].index() != 0 || get<MSTP_TokenInfo*>(list[2])->OprtID != MSTP_ParenL) {
        cout << "parse error" << endl;
        return {};
      }
      int j;
      for (j = 3; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenR) {
            break;
          } else if (idop == MSTP_Comma) {
            continue;
          } else {
            cout << "parse error" << endl;
            return {};
          }
        } else {
          if (get<MST_Object*>(list[j])->Type != MST_SymbolReference) {
            cout << "parse error" << endl;
            return {};
          }
          funcargs.push_back(get<MST_Object*>(list[j]));
        }
      }
      if (j >= list.size() || list[j].index() != 0 || get<MSTP_TokenInfo*>(list[j])->OprtID != MSTP_ParenR) {
        cout << "parse error" << endl;
        return {};
      }
      continue;
    } else if (fwid == MSTP_If) {
      ifnest.push_back(cnest+1);
      ifthen.push_back({{}});
      vector<variant<MSTP_TokenInfo*, MST_Object*>> cond;
      int parl = 0;
      if (list[1].index() == 0 && get<MSTP_TokenInfo*>(list[1])->OprtID == MSTP_ParenL) parl = 1;
      int j;
      for (j = 1+parl; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenL) parl++;
          if (idop == MSTP_ParenR) {
            if (parl <= 1) break;
            parl--;
          }
        }
        cond.push_back(list[j]);
      }
      Error = 0;
      vector<MST_Object*> p = Parse2(cond, atnest || deftask);
      if (p.size() != 1 || Error) {
        cout << "parse error" << endl;
        return {};
      }
      ifcond.push_back({p[0]});
      continue;
    } else if (fwid == MSTP_Else) {
      ifthen.back().push_back({});
      continue;
    } else if (fwid == MSTP_For) {
      fornest.push_back(cnest+1);
      forexpr.push_back({});
      int parl = 0;
      if (list[1].index() == 0 && get<MSTP_TokenInfo*>(list[1])->OprtID == MSTP_ParenL) parl = 1;
      if (list[1+parl].index() == 0) {
        cout << "parse error" << endl;
        return {};
      }
      forcnt.push_back(get<MST_Object*>(list[1+parl]));
      vector<variant<MSTP_TokenInfo*, MST_Object*>> max;
      int mparl = 0;
      for (int j = 2+parl; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenL) mparl++;
          if (idop == MSTP_ParenR) {
            if (mparl <= 1) break;
            mparl--;
          }
        }
        max.push_back(list[j]);
      }

      if (max.size()) {
        Error = 0;
        vector<MST_Object*> p = Parse2(max, atnest || deftask);
        if (p.size() != 1 || Error) {
          cout << "parse error" << endl;
          return {};
        }
        formax.push_back(p[0]);
      } else {
        formax.push_back(get<MST_Object*>(max[0]));
      }
      continue;
    }
    Error = 0;
    vector<MST_Object*> p = Parse2(list, atnest || deftask);
    if (Error) {
      cout << "parse error" << endl;
      return {};
    }
    if (fornest.size() && lastnest == 4) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j]->Type == MST_Expression) {
          forexpr.back().push_back((MST_Expr*)p[j]);
        } else {
          FreeMST_Object(p[j]);
        }
      }
    } else if (ifnest.size() && lastnest == 3) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j]->Type == MST_Expression) {
          ifthen.back().back().push_back((MST_Expr*)p[j]);
        } else {
          FreeMST_Object(p[j]);
        }
      }
    } else if (atnest && lastnest == 1) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j]->Type == MST_Expression) {
          trgtask.push_back(p[j]);
        } else {
          FreeMST_Object(p[j]);
        }
      }
    } else if (defun || deftask) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j]->Type == MST_Expression) {
          funcexpr.push_back((MST_Expr*)p[j]);
        } else {
          FreeMST_Object(p[j]);
        }
      }
    } else {
      for (int j = 0; j < p.size(); j++) {
        ret.push_back(p[j]);
      }
    }
  }
  return ret;
}

vector<MST_Object*> MST_Parser::Parse2(vector<variant<MSTP_TokenInfo*, MST_Object*>>& list, int mode) {
  int s, e;
  int idl, idr;
  if (list.size() < 1) {
    return {};
  }
  for (s = list.size() - 1; 0 <= s; s--) {
    idr = -1;
    idl = -1;
    if (list[s].index() == 0) {
      idl = get<MSTP_TokenInfo*>(list[s])->OprtID;
    }
    if (idl == MSTP_BracketL || idl == MSTP_ParenL || idl == MSTP_CurlyBracketL) {
      for (e = s; e < list.size(); e++) {
        if (list[e].index() != 0) continue;
        idr = get<MSTP_TokenInfo*>(list[e])->OprtID;
        if (idl + 1 == idr) break;
      }
      if (e == list.size()) {
        cout << "parse error" << endl;
        return {};
      }
    } else if (s == 0) {
      s = -1;
      e = list.size();
    } else {
      continue;
    }

    vector<variant<MSTP_TokenInfo*, MST_Object*>> list2 = {};
    if (e-s>1) {
      for (int i = e - 1; s < i; i--) {
        if (list[i].index() != 0) {
          list2.push_back(list[i]);
          continue;
        }
        int idop = get<MSTP_TokenInfo*>(list[i])->OprtID;
        if (idop == MSTP_LNot || idop == MSTP_BNot || idop == MSTP_Dollar) {
          if (list2.size() == 0 || list2.back().index() == 0) {
            cout << "parse error" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          MST_Expr* expr = AllocMST_Expr(1);
          if (idop == MSTP_LNot) {
            expr->Operator = MST_LNot;
          } else if (idop == MSTP_BNot){
            expr->Operator = MST_BNot;
          } else {
            expr->Operator = MST_GetInt;
          }
          expr->Operands[0] = get<MST_Object*>(list2.back());
          list2.back() = (MST_Object*)expr;
        } else {
          list2.push_back(list[i]);
        }
      }
    }

    static vector<vector<int>> opmstp
      = {{MSTP_Mul, MSTP_Div, MSTP_Pow},
         {MSTP_Add, MSTP_Sub},
         {MSTP_ShiftL, MSTP_ShiftR},
         {MSTP_Greater, MSTP_GE, MSTP_Lesser, MSTP_LE},
         {MSTP_Equal, MSTP_NE},
         {MSTP_BAnd, MSTP_BOr},
         {MSTP_LAnd, MSTP_LOr},
         {MSTP_Set, MSTP_DollarEq,
          MSTP_SetAdd, MSTP_SetSub, MSTP_SetMul, MSTP_SetDiv, MSTP_SetPow,
          MSTP_SetBAnd, MSTP_SetBOr, MSTP_SetXor, MSTP_SetLAnd, MSTP_SetLOr}};

    static vector<vector<enum MST_Operator>> opmst
      = {{MST_Mul, MST_Div, MST_Pow},
         {MST_Add, MST_Sub},
         {MST_ShiftL, MST_ShiftR},
         {MST_Greater, MST_GE, MST_Lesser, MST_LE},
         {MST_Equal, MST_NE},
         {MST_BAnd, MST_BOr},
         {MST_LAnd, MST_LOr},
         {MST_Set, MST_Set,
          MST_Add, MST_BOr, MST_Mul, MST_Div, MST_Pow,
          MST_BAnd, MST_BOr, MST_Xor, MST_LAnd, MST_LOr}};

    if (list2.size()) {
      vector<variant<MSTP_TokenInfo*, MST_Object*>> list3 = {};
      for (int i = 0; i < opmstp.size(); i++) {
        list3 = {};
        for (int j = 0; j < list2.size(); j++) {
          if (list2[j].index() == 0) {
            int idop = get<MSTP_TokenInfo*>(list2[j])->OprtID;
            int found = 0;
            for (int k = 0; k < opmstp[i].size(); k++) {
              if (idop == opmstp[i][k]) {
                if (list3.size() == 0 || j+1 == list2.size() || list3.back().index() == 0) {
                  cout << "parse error" << endl;
                  if (Mode) {
                    Error = 1;
                    return {};
                  } else {
                    exit(-1);
                  }
                }
                MST_Object* expr;
                if (idop == MSTP_Set) {
                  if (mode) {
                    expr = MST_Expr2(MST_Set, get<MST_Object*>(list2[j+1]), get<MST_Object*>(list3.back()));
                  } else {
                    expr = MST_Expr2(MST_Bind, get<MST_Object*>(list2[j+1]), get<MST_Object*>(list3.back()));
                  }
                } else if (MSTP_SetAdd <= idop && idop <= MSTP_SetLOr) {
                  MST_Object* expr2 = MST_Expr2(opmst[i][k], get<MST_Object*>(list2[j+1]), get<MST_Object*>(list3.back()));
                  if (mode) {
                    expr = MST_Expr2(MST_Set, CopyMST_Object(get<MST_Object*>(list2[j+1])), expr2);
                  } else {
                    expr = MST_Expr2(MST_Bind, CopyMST_Object(get<MST_Object*>(list2[j+1])), expr2);
                  }
                } else {
                  expr = MST_Expr2(opmst[i][k], get<MST_Object*>(list2[j+1]), get<MST_Object*>(list3.back()));
                }
                list3.back() = expr;
                j++;
                found = 1;
                break;
              }
            }
            if (!found) {
              list3.push_back(list2[j]);
            }
          } else {
            list3.push_back(list2[j]);
          }
        }
        list2 = list3;
      }
    }

    if (idl == MSTP_BracketL) {
      if (s > 0 && list[s-1].index() == 1) {
        if (list2.size() == 1) {
          if (list2[0].index() != 1) {
            cout << "parse error" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          MST_ObjRef* ref = AllocMST_ObjRef();
          ref->Object.Ptr = get<MST_Object*>(list[s-1]);
          ref->Index = get<MST_Object*>(list2[0]);
          vector<variant<MSTP_TokenInfo*, MST_Object*>> list4;
          for (int i = 0; i < s - 1; i++) {
            list4.push_back(list[i]);
          }
          list4.push_back((MST_Object*)ref);
          for (int i = e + 1; i < list.size(); i++) {
            list4.push_back(list[i]);
          }
          list = list4;
        } else if (list2.size() == 3) {
          if (list2[0].index() != 1 || list2[1].index() != 0 || list2[2].index() != 1) {
            cout << "parse error" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          MST_ObjRef* ref = AllocMST_ObjRef();
          ref->Object.Ptr = get<MST_Object*>(list[s-1]);
          ref->Index = get<MST_Object*>(list2[2]);
          int idop = get<MSTP_TokenInfo*>(list2[1])->OprtID;
          if (idop == MSTP_PlusSemicolon) {
            ref->Width = get<MST_Object*>(list2[0]);
          } else if (idop == MSTP_MinusSemicolon) {
            MST_Expr* expr = AllocMST_Expr(2);
            expr->Operator = MST_Sub;
            expr->Operands[0] = AllocMST_Val(32);
            expr->Operands[1] = get<MST_Object*>(list2[0]);
            ref->Width = (MST_Object*)expr;
            *((int*)(expr->Operands[0]->Ptr)) = 0;
          } else if (idop == MSTP_Semicolon) {
            MST_Expr* expr1 = AllocMST_Expr(2);
            MST_Expr* expr2 = AllocMST_Expr(2);
            expr2->Operator = MST_Sub;
            expr2->Operands[0] = get<MST_Object*>(list2[2]);
            expr2->Operands[1] = get<MST_Object*>(list2[0]);
            expr1->Operator = MST_Add;
            expr1->Operands[0] = (MST_Object*)expr2;
            expr1->Operands[1] = AllocMST_Val(32);
            *((int*)(expr1->Operands[1]->Ptr)) = 1;
            ref->Width = (MST_Object*)expr1;
            ref->Index = get<MST_Object*>(list2[0]);
          } else {
            cout << "parse error" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          vector<variant<MSTP_TokenInfo*, MST_Object*>> list4;
          for (int i = 0; i < s - 1; i++) {
            list4.push_back(list[i]);
          }
          list4.push_back((MST_Object*)ref);
          for (int i = e + 1; i < list.size(); i++) {
            list4.push_back(list[i]);
          }
          list = list4;
        } else {
          cout << "parse error" << endl;
          if (Mode) {
            Error = 1;
            return {};
          } else {
            exit(-1);
          }
        }

      } else {
        vector<MST_Object*> nitems = {};
        for (int i = 0; i < list2.size(); i++) {
          if (list2[i].index() == 0) {
            if (get<MSTP_TokenInfo*>(list2[i])->OprtID == MSTP_Comma) {
              continue;
            } else {
              cout << "parse error" << endl;
              if (Mode) {
                Error = 1;
                return {};
              } else {
                exit(-1);
              }
            }
          }
          nitems.push_back(get<MST_Object*>(list2[list2.size() - i -1]));
        }
        int port = 0;
        if (s > 0 && list[s-1].index() == 0) {
           int pid = get<MSTP_TokenInfo*>(list[s-1])->WordID;
           if (pid == MSTP_In) {
             port = MST_Input;
           } else if (pid == MSTP_Out) {
             port = MST_Output;
           } else if (pid == MSTP_IO) {
             port = MST_Inout;
           }
        }
        MST_Expr* expr = AllocMST_Expr(nitems.size() + !!port);
        expr->Operator = port ? MST_NewPort : MST_NewObj;
        for (int i = 0; i < nitems.size(); i++) {
          expr->Operands[i+ !!port] = nitems[i];
        }
        if (port) {
          MST_Object* val = AllocMST_Val(32);
          expr->Operands[0] = val;
          *((int*)val->Ptr) = port;
        }
        vector<variant<MSTP_TokenInfo*, MST_Object*>> list4 = {};
        for (int i = 0; i < s - !!port; i++) {
          list4.push_back(list[i]);
        }
        list4.push_back((MST_Object*)expr);
        for (int i = e + 1; i < list.size(); i++) {
          list4.push_back(list[i]);
        }
        list = list4;
      }
    } else if (idl == MSTP_ParenL) {
      if (s > 0 && list[s-1].index() == 1) {
        vector<MST_Object*> args;
        for (int i = 0; i < list2.size(); i++) {
          if (list2[i].index() == 0) {
            if (get<MSTP_TokenInfo*>(list2[i])->OprtID == MSTP_Comma) {
              continue;
            } else {
              cout << "parse error" << endl;
              if (Mode) {
                Error = 1;
                return {};
              } else {
                exit(-1);
              }
            }
          }
          args.push_back(get<MST_Object*>(list2[list2.size() - i -1]));
        }
        if (s > 2 && list[s-2].index() == 0
            && get<MSTP_TokenInfo*>(list[s-2])->OprtID == MSTP_Piriod
            && list[s-3].index() == 1) {
          MST_Expr* expr = AllocMST_Expr(args.size()+2);
          expr->Operator = MST_MCall;
          expr->Operands[0] = get<MST_Object*>(list[s-1]);
          expr->Operands[1] = get<MST_Object*>(list[s-3]);
          for (int i = 0 ; i < args.size(); i++) {
            expr->Operands[i+2] = args[i];
          }
          vector<variant<MSTP_TokenInfo*, MST_Object*>> list4 = {};
          for (int i = 0; i < s - 3; i++) {
            list4.push_back(list[i]);
          }
          list4.push_back((MST_Object*)expr);
          for (int i = e + 1; i < list.size(); i++) {
            list4.push_back(list[i]);
          }
          list = list4;
        } else {
          MST_Expr* expr = AllocMST_Expr(args.size()+1);
          expr->Operator = MST_Call;
          expr->Operands[0] = get<MST_Object*>(list[s-1]);
          for (int i = 0; i < args.size(); i++) {
            expr->Operands[i+1] = args[i];
          }
          vector<variant<MSTP_TokenInfo*, MST_Object*>> list4 = {};
          for (int i = 0; i < s - 1; i++) {
            list4.push_back(list[i]);
          }
          list4.push_back((MST_Object*)expr);
          for (int i = e + 1; i < list.size(); i++) {
            list4.push_back(list[i]);
          }
          list = list4;
        }
      } else {
        if (list2.size() != 1 || list2[0].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            Error = 1;
            return {};
          } else {
            exit(-1);
          }
        }
        vector<variant<MSTP_TokenInfo*, MST_Object*>> list4 = {};
        for (int i = 0; i < s; i++) {
          list4.push_back(list[i]);
        }
        list4.push_back(list2[0]);
        for (int i = e + 1; i < list.size(); i++) {
          list4.push_back(list[i]);
        }
        list = list4;
      }
      if (!s) s = 1;
    } else if (idl == MSTP_CurlyBracketL) {
      vector<MST_Object*> items = {};
      for (int i = 0; i < list2.size(); i++) {
        if (list2[i].index() == 0) {
          if (get<MSTP_TokenInfo*>(list2[i])->OprtID == MSTP_Comma) {
            continue;
          }
          cout << "parse error" << endl;
          if (Mode) {
            Error = 1;
            return {};
          } else {
            exit(-1);
          }
        }
        if (list2[i].index() == 1) {
          items.push_back(get<MST_Object*>(list2[i]));
        }
      }
      MST_Lst* lst = AllocMST_Lst(items.size());
      for (int i = 0; i < items.size(); i++) {
        lst->Items[i] = items[items.size()-i-1];
      }
      vector<variant<MSTP_TokenInfo*, MST_Object*>> list4 = {};
      for (int i = 0; i < s; i++) {
        list4.push_back(list[i]);
      }
      list4.push_back((MST_Object*)lst);
      for (int i = e + 1; i < list.size(); i++) {
        list4.push_back(list[i]);
      }
      list = list4;
      if (!s) s = 1;
    } else {
      vector<MST_Object*> ret = {};
      for (int i = list2.size()-1; 0 <= i; i--) {
        if (list2[i].index() == 0) {
          if (get<MSTP_TokenInfo*>(list2[i])->OprtID == MSTP_Comma) {
            continue;
          }
          if (get<MSTP_TokenInfo*>(list2[i])->OprtID == MSTP_Colon) {
            MST_Str* str = AllocMST_Str(6);
            strcpy(str->Data, "waitev");
            MST_Object* ref = (MST_Object*)malloc(sizeof(MST_Object));
            ref->Type = MST_SymbolReference;
            ref->Ptr = str;
            MST_Expr* expr = AllocMST_Expr(1);
            expr->Operator = MST_Call;
            expr->Operands[0] = ref;
            ret.push_back((MST_Object*)expr);
            continue;
          }
          cout << "parse error" << endl;
          if (Mode) {
            Error = 1;
            return {};
          } else {
            exit(-1);
          }
        }
        ret.push_back(get<MST_Object*>(list2[i]));
      }
      return ret;
    }
  }
  if (Mode) {
    Error = 1;
    return {};
  } else {
    exit(-1);
  }
}

vector<MST_Object*> MSTP_Parse(char* src) {
  return mstp->Parse(src);
}

vector<MST_Object*> MSTP_Read() {
  char buff[0xffff];
  int n = 0;
  int ll = 0;
  int npar = 0;
  int nbl = 0;
  int nest = 0;
  int sem = 0;
  int c = 0;
  while(1) {
    if (n > 0xfffe) {
      return {};
    }
    sem = 0;
    if (c == ':') sem = 1;
    c = getchar();
    buff[n++] = c;
    switch (c) {
      case ' ':
        if (!ll) nest |= 1;
        break;
      case '\t':
        if (!ll) nest |= 1;
        break;
      case '(':
        npar++;
        break;
      case ')':
        npar--;
        break;
      case '[':
        nbl++;
        break;
      case ']':
        nbl--;
        break;
    }
    if (c == '\n') {
      if ((!ll || !nest) && !npar && !nbl && !sem) {
        break;
      } else {
        ll = 0;
        nest = 0;
      }
    } else {
      ll++;
    }
  }
  buff[n] = 0;
  return MSTP_Parse(buff);
}

MST_Object* TimingChart(int nargs, MST_Object** args) {
  double unit = 200;
  int l = 0;
  MST_Lst** lst = (MST_Lst**)args;
  for (int i = 0; i < nargs; i++) {
    if (args[i]->Type != MST_List) {
      return NULL;
    }
    if (lst[i]->nItems > l) {
      l = lst[i]->nItems;
    }
  }
  ofstream ofs(string("timingchart.svg"));
  if (!ofs) {
    return NULL;
  }
  ofs << "<?xml version=\"1.0\"?><!DOCTYPE svg PUBLIC \"-//W3C//DTD SVG 1.1//EN\" \"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd\">";
  ofs << "<svg width=\"" << (l+2) * unit << "\" height=\"" << nargs * unit * 2 << "\" xmlns=\"http://www.w3.org/2000/svg\" style=\"background-color:black;\">";
  for (int i = 0; i < nargs; i++) {
    ofs << "<rect x=\"" << unit << "\" y=\"" << (unit*2*i) + (unit/2) << "\" width=\"" << l*unit << "\" height=\"" << unit
        << "\" style=\"stroke: darkgreen; stroke-width:2; fill:none\"/>";
    vector<int> val = {};
    double max = 1.0;
    for (int j = 0; j < lst[i]->nItems; j++) {
      val.push_back(GetIntMST_Obj(lst[i]->Items[j]));
      if (val.back() > max) max = val.back();
      if (j) {
        ofs << "<line x1=\"" << unit+(unit*j) << "\" x2=\"" << unit+(unit*j) << "\" y1=\"" << (unit*2*i)+(unit/2) << "\" y2=\"" << (unit*2*i)+(unit*3/2) << "\""
            << " style=\"stroke: darkgreen; stroke-width:2;stroke-dasharray: 20 10;\"/>";
      }
    }
    ofs << "<path d=\"";
    for (int j = 0; j < val.size(); j++) {
      if (!j) ofs << " M " << (j+1)*unit << " " << (unit*2*i) + (unit*3/2) - (val[j]/max)*unit;
      ofs << " L " << (j+2)*unit << " " << (unit*2*i) + (unit*3/2) - (val[j]/max)*unit;
      if (j+1 < val.size()) {
        ofs << " L " << (j+2)*unit << " " << (unit*2*i) + (unit*3/2) - (val[j+1]/max)*unit;
      }
    }
    ofs << "\" style=\"stroke: green; stroke-width:8; fill:none\"/>";
  }
  ofs << "</svg>";
  return NULL;
}
