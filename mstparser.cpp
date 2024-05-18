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
  static vector<string> oprt = {"=", "+", "-", "*", "/", "**", "&", "|", "^", "&&", "||", "~", "!", "==", "!=", ">", ">=", "<", "<=", "<<", ">>", "[", "]", "(", ")", " ", "\t", "\n", ":", ",", "0x", "$", "$=", "{", "}", "+:", "-:", ".", ";", ":;", "+=", "-=", "*=", "/=", "**=", "&=", "|=", "^=", "&&=", "||="};
  for (int i = 0; i < oprt.size(); i++) {
    MSTP_TokenInfo* info = new MSTP_TokenInfo;
    OprtTable.Get(oprt[i]) = info;
    Operators.push_back(info);
    info->OprtID = i;
    info->WordID = -1;
  }
  static vector<string> words = {"in", "out", "io", "at", "pos", "neg", "defun", "if", "else", "elif", "for", "deftask", "cwk"};
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

int MST_Parser::SetMode(int m) {
  Mode = m;
  return 0;
}

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
  int cwknest = 0;

  vector<pair<int,MST_Object*>> triggers = {};
  vector<MST_Object*> trgtask = {};

  CwkCnt = NULL;
  nState = 0;

  vector<vector<MST_Object*>> cwktask = {};


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
          int* v = (int*)val->Ptr;
          *v = 0;
          for (int k = 0; k < tokens[n].Len; k++) {
            *v *= 10;
            if (!('0' <= ptr[k] && ptr[k] <= '9')) {
              cout << "parse error" << endl;
              if (Mode) {
                return {};
              } else {
                exit(-1);
              }
            }
            *v += ptr[k] - '0';
          }
          list.push_back(val);
        } else {
          MST_Object* sym = (MST_Object*)malloc(sizeof(MST_Object));
          if (sym == NULL) {
            cout << "allocation error" << endl;
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
          MST_Str* str = AllocMST_Str(tokens[n].Len);
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

    int lastnest = 0; //0: none, 1:at, 2: defun, 3:if, 4:for 5:deftask 6:cwk
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

      if (cwknest && cwknest > dep) {
        if (lastnest) {
          secnest = lastnest;
          secdep = dep;
        }
        lastnest = 6;
        dep = cwknest;
      } else if (cwknest && cwknest > secdep) {
        secnest = 6;
        secdep = cwknest;
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

      if (ifnest.size() && ifnest.back() > cnest + (fwid == MSTP_Else || fwid == MSTP_Elif) && lastnest == 3) {
        MST_Expr* expr = AllocMST_Expr(1 + ifthen.back().size());
        expr->Operator = MST_If;
        if (ifcond.back().size() == 1) {
          expr->Operands[0] = ifcond.back().back();
        } else {
          MST_Lst* clst = AllocMST_Lst(ifcond.back().size());
          for (int j = 0; j < ifcond.back().size(); j++) {
            clst->Items[j] = ifcond.back()[j];
          }
          expr->Operands[0] = (MST_Object*)clst;
        }
        for (int j = 0; j < ifthen.back().size(); j++) {
          MST_Expr* prog = AllocMST_Expr(ifthen.back()[j].size());
          expr->Operands[j+1] = (MST_Object*)prog;
          prog->Operator = MST_Progn;
          for (int k = 0; k < ifthen.back()[j].size(); k++) {
            prog->Operands[k] = (MST_Object*)ifthen.back()[j][k];
          }
        }
        ifcond.pop_back();
        ifnest.pop_back();
        ifthen.pop_back();
        if (secnest == 1) {
          trgtask.push_back((MST_Object*)expr);
        } else if (secnest == 6) {
          cwktask.back().push_back((MST_Object*)expr);
          if (CLFlag) {
            nState++;
            CLFlag = 0;
            cwktask.push_back({});
          }
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
        } else if (secnest == 6) {
          cwktask.back().push_back((MST_Object*)expr);
          if (CLFlag) {
            nState++;
            CLFlag = 0;
            cwktask.push_back({});
          }
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

      if (cwknest && cwknest > cnest && lastnest == 6) {
        cwknest = 0;
        MST_Expr* expr = AllocMST_Expr(cwktask.size()+1);
        expr->Operator = MST_If;
        MST_Lst* lst = AllocMST_Lst(cwktask.size());
        expr->Operands[0] = (MST_Object*)lst;
        for (int j = 0; j < cwktask.size(); j++) {
          MST_Expr* cond = AllocMST_Expr(2);
          cond->Operator = MST_Equal;
          cond->Operands[0] = CopyMST_Object(CwkCnt);
          cond->Operands[1] = AllocMST_Val(32);
          *((int*)cond->Operands[1]->Ptr) = j;
          lst->Items[j] = (MST_Object*)cond;
          MST_Expr* prog = AllocMST_Expr(cwktask[j].size());
          prog->Operator = MST_Progn;
          for (int k = 0; k < cwktask[j].size(); k++) {
            prog->Operands[k] = (MST_Object*)cwktask[j][k];
          }
          expr->Operands[j+1] = (MST_Object*)prog;
        }

        MST_Expr* exprat = AllocMST_Expr(2);
        exprat->Operator = MST_AddTrgTask;
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
        exprat->Operands[0] = (MST_Object*)trglist;
        exprat->Operands[1] = (MST_Object*)expr;

        FreeMST_Object(CwkCnt);
        CwkCnt = NULL;
        nState = 0;

        if (secnest == 3) {
          ifthen.back().back().push_back(exprat);
        } else if (secnest == 2 || secnest == 5) {
          funcexpr.push_back(exprat);
        } else if (secnest == 4) {
          forexpr.back().push_back(exprat);
        } else {
          ret.push_back((MST_Object*)exprat);
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
      if (atnest || cwknest || list.size() == 1) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      atnest = cnest + 1;
      triggers = {};
      trgtask = {};
      CwkCnt = NULL;
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
              if (Mode) {
                return {};
              } else {
                exit(-1);
              }
            }
            j++;
            break;
          } else if (idop == MSTP_Comma) {
            continue;
          }

          int idwd = get<MSTP_TokenInfo*>(list[j])->WordID;
          if (idwd == MSTP_Pos || idwd == MSTP_Neg) {
            if (j+1 >= list.size() || list[j+1].index() != 1) {
              cout << "parse error" << endl;
              if (Mode) {
                return {};
              } else {
                exit(-1);
              }
            }
            triggers.push_back({idwd, get<MST_Object*>(list[j+1])});
            j++;
            continue;
          }
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        } else {
          triggers.push_back({-1, get<MST_Object*>(list[j])});
        }
      }
      if (j < list.size()) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_Colon) j++;
        }
      }
      if (j < list.size()) {
        vector<variant<MSTP_TokenInfo*, MST_Object*>> t = {};
        for (; j < list.size(); j++) {
          t.push_back(list[j]);
        }
        Error = 0;
        t = ParseExpr(t, atnest || cwknest || deftask);
        if (Error) {
          return {};
        }
        for (j = 0; j < t.size(); j++) {
          if (t[j].index() == 1) {
            MST_Object* obj = get<MST_Object*>(t[j]);
            if (obj->Type == MST_Expression) {
              trgtask.push_back(obj);
            } else {
              FreeMST_Object(obj);
            }
          } else {
            cout << "parse error" << endl;
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
        }
      }
      continue;
    } else if (fwid == MSTP_ClockWork) {
      if (atnest || cwknest || list.size() == 1) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      cwknest = cnest + 1;
      triggers = {};
      cwktask = {{}};
      nState = 0;
      CLFlag = 0;
      int parl = 0;
      int j = 1;
      if (list[1].index() == 0 && get<MSTP_TokenInfo*>(list[1])->OprtID == MSTP_ParenL) {
        parl = 1;
        j = 2;
      }
      if (list[j].index() != 1) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      CwkCnt = get<MST_Object*>(list[j]);
      j++;
      for (; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenR) {
            if (!parl) {
              cout << "parse error" << endl;
              if (Mode) {
                return {};
              } else {
                exit(-1);
              }
            }
            parl--;
            if (!parl) {
              j++;
              break;
            }
          } else if (idop == MSTP_Comma) {
            continue;
          }

          int idwd = get<MSTP_TokenInfo*>(list[j])->WordID;
          if (idwd == MSTP_Pos || idwd == MSTP_Neg) {
            if (j+1 >= list.size() || list[j+1].index() != 1) {
              cout << "parse error" << endl;
              if (Mode) {
                return {};
              } else {
                exit(-1);
              }
            }
            triggers.push_back({idwd, get<MST_Object*>(list[j+1])});
            j++;
            continue;
          }
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        } else {
          triggers.push_back({-1, get<MST_Object*>(list[j])});
        }
      }
      MST_Expr* expr1 = AllocMST_Expr(2);
      MST_Expr* expr2 = AllocMST_Expr(1);
      expr2->Operator = MST_NewObj;
      expr2->Operands[0] = AllocMST_Val(32);
      *((int*)expr2->Operands[0]->Ptr) = 32;
      expr1->Operator = MST_Bind;
      expr1->Operands[0] = CopyMST_Object(CwkCnt);
      expr1->Operands[1] = (MST_Object*)expr2;
      if (fornest.size() && lastnest == 4) {
        forexpr.back().push_back((MST_Expr*)expr1);
      } else if (ifnest.size() && lastnest == 3) {
        ifthen.back().back().push_back(expr1);
      } if (defun || deftask) {
        funcexpr.push_back(expr1);
      } else {
        ret.push_back((MST_Object*)expr1);
      }
      if (j < list.size()) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_Colon) {
            j++;
          }
        }
      }
      if (j < list.size()) {
        vector<variant<MSTP_TokenInfo*, MST_Object*>> t = {};
        for (; j < list.size(); j++) {
          t.push_back(list[j]);
        }
        Error = 0;
        t = ParseExpr(t, atnest || cwknest || deftask);
        if (Error) {
          return {};
        }
        for (j = 0; j < t.size(); j++) {
          if (t[j].index() == 1) {
            MST_Object* obj = get<MST_Object*>(t[j]);
            if (obj->Type == MST_Expression) {
              cwktask.back().push_back(obj);
            } else {
              FreeMST_Object(obj);
            }
          } else {
            cout << "parse error" << endl;
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
        }
        if (CLFlag) {
          cwktask.push_back({});
          nState++;
          CLFlag = 0;
        }
      }
      continue;
    } else if (fwid == MSTP_Defun || fwid == MSTP_Deftask) {
      if (defun || atnest || cwknest || deftask || ifnest.size()) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      if (list.size() < 4) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
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
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      funcname = get<MST_Object*>(list[1]);
      if (list[2].index() != 0 || get<MSTP_TokenInfo*>(list[2])->OprtID != MSTP_ParenL) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
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
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
        } else {
          if (get<MST_Object*>(list[j])->Type != MST_SymbolReference) {
            cout << "parse error" << endl;
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
          funcargs.push_back(get<MST_Object*>(list[j]));
        }
      }
      if (j >= list.size() || list[j].index() != 0 || get<MSTP_TokenInfo*>(list[j])->OprtID != MSTP_ParenR) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      continue;
    } else if (fwid == MSTP_If) {
      ifnest.push_back(cnest+1);
      ifthen.push_back({{}});
      vector<variant<MSTP_TokenInfo*, MST_Object*>> cond = {};
      int j;
      int parl = 0;
      for (j = 1; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenL) {
            parl++;
          }
          if (idop == MSTP_ParenR) {
            if (!parl) {
              cout << "unbalanced parentheses" << endl;
              if (Mode) {
                return {};
              } else {
                exit(-1);
              }
            }
            parl--;
            if (!parl) {
              cond.push_back(list[j]);
              j++;
              break;
            }
          }
          if (j+1 == list.size()) {
            if (idop == MSTP_Colon) {
              break;
            }
          }
        }
        cond.push_back(list[j]);
      }
      if (parl) {
        cout << "unbalanced parentheses" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      if (!cond.size()) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      Error = 0;
      cond = ParseExpr(cond, atnest || cwknest || deftask);
      if (cond.size() != 1 || Error || cond[0].index() != 1) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      ifcond.push_back({get<MST_Object*>(cond[0])});
      if (j < list.size()) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_Colon) j++;
        }
      }
      if (j < list.size()) {
        cond = {};
        for (; j < list.size(); j++) {
          cond.push_back(list[j]);
        }
        Error = 0;
        cond = ParseExpr(cond, atnest || cwknest || deftask);
        if (Error) {
          cout << "parse error" << endl;
          return {};
        }
        for (j = 0; j < cond.size(); j++) {
          if (cond[j].index() != 1) {
            cout << "parse error" << endl;
            return {};
          }
          MST_Object* c = get<MST_Object*>(cond[j]);
          if (c->Type == MST_Expression) {
            ifthen.back().back().push_back((MST_Expr*)c);
          } else {
            FreeMST_Object(c);
          }
        }
      }
      continue;
    } else if (fwid == MSTP_Else || fwid == MSTP_Elif) {
      if (!ifnest.size() || ifnest.back() != cnest + 1) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      ifthen.back().push_back({});
      int j = 0;
      if (fwid != MSTP_Elif && 1 < list.size() && list[1].index() == 0) {
        int wdop = get<MSTP_TokenInfo*>(list[1])->WordID;
        if (wdop == MSTP_If) {
          j = 1;
        }
      }
      vector<variant<MSTP_TokenInfo*, MST_Object*>> cond = {};
      if (j || fwid == MSTP_Elif) {
        int parl = 0;
        for (j = j + 1; j < list.size(); j++) {
          if (list[j].index() == 0) {
            int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
            if (idop == MSTP_ParenL) {
              parl++;
            }
            if (idop == MSTP_ParenR) {
              if (!parl) {
                cout << "unbalanced parentheses" << endl;
                if (Mode) {
                  return {};
                } else {
                  exit(-1);
                }
              }
              parl--;
              if (!parl) {
                cond.push_back(list[j]);
                j++;
                break;
              }
            }
            if (j+1 == list.size()) {
              if (idop == MSTP_Colon) {
                break;
              }
            }
          }
          cond.push_back(list[j]);
        }
        Error = 0;
        cond = ParseExpr(cond, atnest || cwknest || deftask);
        if (cond.size() != 1 || Error || cond[0].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        ifcond.back().push_back(get<MST_Object*>(cond[0]));
      } else {
        j = 1;
      }
      if (j < list.size()) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_Colon) j++;
        }
      }
      if (j < list.size()) {
        cond = {};
        for (; j < list.size(); j++) {
          cond.push_back(list[j]);
        }
        Error = 0;
        cond = ParseExpr(cond, atnest || cwknest || deftask);
        if (Error) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        for (j = 0; j < cond.size(); j++) {
          if (cond[j].index() != 1) {
            cout << "parse error" << endl;
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
          MST_Object* c = get<MST_Object*>(cond[j]);
          if (c->Type == MST_Expression) {
            ifthen.back().back().push_back((MST_Expr*)c);
          } else {
            FreeMST_Object(c);
          }
        }
      }
      continue;
    } else if (fwid == MSTP_For) {
      fornest.push_back(cnest+1);
      forexpr.push_back({});
      int parl = 0;
      if (list[1].index() == 0 && get<MSTP_TokenInfo*>(list[1])->OprtID == MSTP_ParenL) parl = 1;
      if (list[1+parl].index() == 0) {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      forcnt.push_back(get<MST_Object*>(list[1+parl]));
      vector<variant<MSTP_TokenInfo*, MST_Object*>> max;
      int mparl = 0;
      int j = parl+2;
      for (; j < list.size(); j++) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_ParenL) mparl++;
          if (idop == MSTP_ParenR) {
            if (!mparl) {
              j++;
              break;
            }
            mparl--;
            if (!mparl) {
              max.push_back(list[j]);
              j++;
              break;
            }
          }
        }
        max.push_back(list[j]);
      }

      if (max.size()) {
        Error = 0;
        max = ParseExpr(max, atnest || cwknest || deftask);
        if (max.size() != 1 || Error || max[0].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        formax.push_back(get<MST_Object*>(max[0]));
      } else {
        cout << "parse error" << endl;
        if (Mode) {
          return {};
        } else {
          exit(-1);
        }
      }
      if (j < list.size()) {
        if (list[j].index() == 0) {
          int idop = get<MSTP_TokenInfo*>(list[j])->OprtID;
          if (idop == MSTP_Colon) {
            j++;
          }
        }
      }
      if (j < list.size()) {
        vector<variant<MSTP_TokenInfo*, MST_Object*>> p;
        for (; j < list.size(); j++) {
          p.push_back(list[j]);
        }
        Error = 0;
        p = ParseExpr(p, atnest || cwknest || deftask);
        if (Error) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        for (j = 0; j < p.size(); j++) {
          if (p[j].index() == 1) {
            MST_Object* obj = get<MST_Object*>(p[j]);
            if (obj->Type == MST_Expression) {
              forexpr.back().push_back((MST_Expr*)obj);
            } else {
              FreeMST_Object(obj);
            }
          } else {
            cout << "parse error" << endl;
            if (Mode) {
              return {};
            } else {
              exit(-1);
            }
          }
        }
      }
      continue;
    }
    Error = 0;
    vector<variant<MSTP_TokenInfo*, MST_Object*>> p = ParseExpr(list, atnest || cwknest || deftask);
    if (Error) {
      cout << "parse error" << endl;
      if (Mode) {
        return {};
      } else {
        exit(-1);
      }
    }
    if (fornest.size() && lastnest == 4) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        MST_Object* obj = get<MST_Object*>(p[j]);
        if (obj->Type == MST_Expression) {
          forexpr.back().push_back((MST_Expr*)obj);
        } else {
          FreeMST_Object(obj);
        }
      }
    } else if (ifnest.size() && lastnest == 3) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        MST_Object* obj = get<MST_Object*>(p[j]);
        if (obj->Type == MST_Expression) {
          ifthen.back().back().push_back((MST_Expr*)obj);
        } else {
          FreeMST_Object(obj);
        }
      }
    } else if (atnest && lastnest == 1) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        MST_Object* obj = get<MST_Object*>(p[j]);
        if (obj->Type == MST_Expression) {
          trgtask.push_back(obj);
        } else {
          FreeMST_Object(obj);
        }
      }
    } else if (cwknest && lastnest == 6) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        MST_Object* obj = get<MST_Object*>(p[j]);
        if (obj->Type == MST_Expression) {
          cwktask.back().push_back(obj);
        } else {
          FreeMST_Object(obj);
        }
      }
      if (CLFlag) {
        nState++;
        CLFlag = 0;
        cwktask.push_back({});
      }
    } else if (defun || deftask) {
      for (int j = 0; j < p.size(); j++) {
        if (p[j].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        MST_Object* obj = get<MST_Object*>(p[j]);
        if (obj->Type == MST_Expression) {
          funcexpr.push_back((MST_Expr*)obj);
        } else {
          FreeMST_Object(obj);
        }
      }
    } else {
      for (int j = 0; j < p.size(); j++) {
        if (p[j].index() != 1) {
          cout << "parse error" << endl;
          if (Mode) {
            return {};
          } else {
            exit(-1);
          }
        }
        ret.push_back(get<MST_Object*>(p[j]));
      }
    }
  }
  return ret;
}

vector<variant<MSTP_TokenInfo*, MST_Object*>> MST_Parser::ParseExpr(vector<variant<MSTP_TokenInfo*, MST_Object*>> list, int mode) {
  while (list.size()) {
    int npar = 0;
    vector<variant<MSTP_TokenInfo*, MST_Object*>> list2 = {};
    int s = -1;
    for (int e = 0; e < list.size(); e++) {
      if (list[e].index() == 0) {
        int idop = get<MSTP_TokenInfo*>(list[e])->OprtID;
        if (idop == MSTP_ParenL) {
          if (!npar) {
            s = e;
            npar = 1;
            continue;
          }
          npar++;
        } else if (idop == MSTP_ParenR) {
          if (!npar) {
            cout << "unbalanced parenthes" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          npar--;
          if (!npar) {
            Error = 0;
            list2 = ParseExpr(list2, mode);
            if (Error) {
              return {};
            }
            if (s && list[s-1].index() == 1 && (get<MST_Object*>(list[s-1])->Type == MST_SymbolReference
                                                || get<MST_Object*>(list[s-1])->Type == MST_ObjectReference)) {
              MST_Expr* expr;
              int m = 0;
              if (s > 2 && list[s-3].index() == 1 && (get<MST_Object*>(list[s-3])->Type == MST_SymbolReference
                                                      || get<MST_Object*>(list[s-3])->Type == MST_ObjectReference)
                        && list[s-2].index() == 0 && get<MSTP_TokenInfo*>(list[s-2])->OprtID == MSTP_Piriod) {
                expr = AllocMST_Expr(list2.size()+2);
                m = 1;
                expr->Operator = MST_MCall;
                expr->Operands[1] = get<MST_Object*>(list[s-3]);
              } else {
                expr = AllocMST_Expr(list2.size()+1);
                expr->Operator = MST_Call;
              }
              expr->Operands[0] = get<MST_Object*>(list[s-1]);
              for (int i = 0; i < list2.size(); i++) {
                if (list2[i].index() != 1) {
                  cout << "error" << endl;
                  if (Mode) {
                    Error = 1;
                    return {};
                  } else {
                    exit(-1);
                  }
                }
                expr->Operands[1+m+i] = get<MST_Object*>(list2[i]);
              }
              list2 = {};
              for (int i = e+1; i < list.size(); i++) {
                list2.push_back(list[i]);
              }
              list.resize(m ? s-3 : s-1);
              list.push_back((MST_Object*)expr);
              for (int i = 0 ; i < list2.size(); i++) {
                list.push_back(list2[i]);
              }
            } else {
              if (list2.size() != 1) {
                cout << "error" << endl;
                if (Mode) {
                  Error = 1;
                  return {};
                } else {
                  exit(-1);
                }
              }
              MST_Object* obj = get<MST_Object*>(list2[0]);
              list2 = {};
              for (int i = e+1; i < list.size(); i++) {
                list2.push_back(list[i]);
              }
              list.resize(s);
              list.push_back(obj);
              for (int i = 0 ; i < list2.size(); i++) {
                list.push_back(list2[i]);
              }
            }
            break;
          }
        }
      }
      if (npar) list2.push_back(list[e]);
    }
    if (npar) {
      cout << "unbalanced parentheses" << endl;
      if (Mode) {
        Error = 1;
        return {};
      } else {
        exit(-1);
      }
    }
    if (s == -1) {
      break;
    }
  }
  while (list.size()) {
    int nbr = 0;
    vector<variant<MSTP_TokenInfo*, MST_Object*>> list2 = {};
    int s = -1;
    for (int e = 0; e < list.size(); e++) {
      if (list[e].index() == 0) {
        int idop = get<MSTP_TokenInfo*>(list[e])->OprtID;
        if (idop == MSTP_BracketL) {
          if (!nbr) {
            s = e;
            nbr = 1;
            continue;
          }
          nbr++;
        } else if (idop == MSTP_BracketR) {
          if (!nbr) {
            cout << "unbalanced brackets" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          nbr--;
          if (!nbr) {
            Error = 0;
            list2 = ParseExpr(list2, mode);
            if (Error) {
              return {};
            }
            if (s && list[s-1].index() == 1 && (get<MST_Object*>(list[s-1])->Type == MST_SymbolReference
                                                || get<MST_Object*>(list[s-1])->Type == MST_ObjectReference)) {
              MST_ObjRef* ref = AllocMST_ObjRef();
              ref->Object.Ptr = get<MST_Object*>(list[s-1]);
              if (list2.size() == 3) {
                if (list2[0].index() != 1 || list2[1].index() != 0 || list2[2].index() != 1) {
                  cout << list2[0].index() << ", " << list2[1].index() << ", " <<  list2[2].index() << endl;
                  cout << "parse error" << endl;
                  if (Mode) {
                    Error = 1;
                    return {};
                  } else {
                    exit(-1);
                  }
                }
                int idop = get<MSTP_TokenInfo*>(list2[1])->OprtID;
                if (idop == MSTP_PlusColon) {
                  ref->Index = get<MST_Object*>(list2[0]);
                  ref->Width = get<MST_Object*>(list2[2]);
                } else if (idop == MSTP_MinusColon) {
                  MST_Expr* expr = AllocMST_Expr(2);
                  expr->Operator = MST_Sub;
                  expr->Operands[0] = AllocMST_Val(32);
                  expr->Operands[1] = get<MST_Object*>(list2[2]);
                  *((int*)(expr->Operands[0]->Ptr)) = 0;

                  ref->Index = get<MST_Object*>(list2[0]);
                  ref->Width = (MST_Object*)expr;
                } else if (idop == MSTP_Colon) {
                  MST_Expr* expr1 = AllocMST_Expr(2);
                  MST_Expr* expr2 = AllocMST_Expr(2);
                  expr2->Operator = MST_Sub;
                  expr2->Operands[0] = get<MST_Object*>(list2[0]);
                  expr2->Operands[1] = get<MST_Object*>(list2[2]);
                  expr1->Operator = MST_Add;
                  expr1->Operands[0] = (MST_Object*)expr2;
                  expr1->Operands[1] = AllocMST_Val(32);
                  *((int*)(expr1->Operands[1]->Ptr)) = 1;

                  ref->Index = get<MST_Object*>(list2[2]);
                  ref->Width = (MST_Object*)expr1;
                } else {
                  cout << "parse error" << endl;
                  if (Mode) {
                    Error = 1;
                    return {};
                  } else {
                    exit(-1);
                  }
                }
              } else if (list2.size() == 1) {
                if (list2[0].index() != 1) {
                  cout << "parse error" << endl;
                  if (Mode) {
                    Error = 1;
                    return {};
                  } else {
                    exit(-1);
                  }
                }
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
              list2 = {};
              for (int i = e+1; i < list.size(); i++) {
                list2.push_back(list[i]);
              }
              list.resize(s-1);
              list.push_back((MST_Object*)ref);
              for (int i = 0 ; i < list2.size(); i++) {
                list.push_back(list2[i]);
              }
            } else {
              int port = 0;
              if (s && list[s-1].index() == 0) {
                int idwd = get<MSTP_TokenInfo*>(list[s-1])->WordID;
                if (idwd == MSTP_In) {
                  port = MST_Input;
                } else if (idwd == MSTP_Out) {
                  port = MST_Output;
                } else if (idwd == MSTP_IO) {
                  port = MST_Inout;
                }
              }
              MST_Expr* expr = AllocMST_Expr(list2.size() + !!port);
              expr->Operator = port ? MST_NewPort : MST_NewObj;
              for (int i = 0; i < list2.size(); i++) {
                if (list2[i].index() != 1) {
                  cout << "parse error" << endl;
                  if (Mode) {
                    Error = 1;
                    return {};
                  } else {
                    exit(-1);
                  }
                }
                expr->Operands[i+!!port] = get<MST_Object*>(list2[i]);
              }
              if (port) {
                MST_Object* val = AllocMST_Val(32);
                expr->Operands[0] = val;
                *((int*)val->Ptr) = port;
              }
              list2 = {};
              for (int i = e+1; i < list.size(); i++) {
                list2.push_back(list[i]);
              }
              list.resize(s-!!port);
              list.push_back((MST_Object*)expr);
              for (int i = 0 ; i < list2.size(); i++) {
                list.push_back(list2[i]);
              }
            }
            break;
          }
          continue;
        }
      }
      if (nbr) list2.push_back(list[e]);
    }
    if (s == -1) break;
  }
  while (list.size()) {
    int ncbr = 0;
    vector<variant<MSTP_TokenInfo*, MST_Object*>> list2 = {};
    int s = -1;
    for (int e = 0; e < list.size(); e++) {
      if (list[e].index() == 0) {
        int idop = get<MSTP_TokenInfo*>(list[e])->OprtID;
        if (idop == MSTP_CurlyBracketL) {
          if (!ncbr) {
            s = e;
            ncbr = 1;
            continue;
          }
          ncbr++;
        } else if (idop == MSTP_CurlyBracketR) {
          if (!ncbr) {
            cout << "unbalanced brackets" << endl;
            if (Mode) {
              Error = 1;
              return {};
            } else {
              exit(-1);
            }
          }
          ncbr--;
          if (!ncbr) {
            Error = 0;
            list2 = ParseExpr(list2, mode);
            if (Error) {
              return {};
            }
            MST_Lst* lst = AllocMST_Lst(list2.size());
            for (int i = 0; i < list2.size(); i++) {
              if (list2[i].index() != 1) {
                cout << "parse error" << endl;
                if (Mode) {
                  Error = 1;
                  return {};
                } else {
                  exit(-1);
                }
              }
              lst->Items[i] = get<MST_Object*>(list2[i]);
            }
            list2 = {};
            for (int i = e+1; i < list.size(); i++) {
              list2.push_back(list[i]);
            }
            list.resize(s);
            list.push_back((MST_Object*)lst);
            for (int i = 0 ; i < list2.size(); i++) {
              list.push_back(list2[i]);
            }
            break;
          }
        }
      }
      if (ncbr) list2.push_back(list[e]);
    }
    if (ncbr) {
      cout << "parse error" << endl;
      if (Mode) {
        Error = 1;
        return {};
      } else {
        exit(-1);
      }
    }
    if (s == -1) break;
  }
  vector<variant<MSTP_TokenInfo*, MST_Object*>> list2 = {};
  while (list.size()) {
    if (list.back().index() == 0) {
      int idop = get<MSTP_TokenInfo*>(list.back())->OprtID;
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
        } else if (idop == MSTP_BNot) {
          expr->Operator = MST_BNot;
        } else {
          expr->Operator = MST_GetInt;
        }
        expr->Operands[0] = get<MST_Object*>(list2.back());
        list2.pop_back();
        list.pop_back();
        list2.push_back((MST_Object*)expr);
        continue;
      }
    }
    list2.push_back(list.back());
    list.pop_back();
  }
  while (list2.size()) {
    list.push_back(list2.back());
    list2.pop_back();
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



  if (list.size()) {
    for (int i = 0; i < opmstp.size(); i++) {
      list2 = {};
      for (int j = 0; j < list.size(); j++) {
        int op = -1;
        if (list[j].index() == 0) op = get<MSTP_TokenInfo*>(list[j])->OprtID;
        if (0 <= op) {
          enum MST_Operator opms = (enum MST_Operator)-1;
          int setn = 0;
          for (int k = 0; k < opmstp[i].size(); k++) {
            if (op == opmstp[i][k]) {
              if (op == MSTP_Set) {
                opms = mode ? MST_Set : MST_Bind;
              } else {
                opms = opmst[i][k];
              }
              if (MSTP_SetAdd <= op && op <= MSTP_SetLOr) {
                setn = 1;
              }
              break;
            }
          }
          if (0 <= opms) {
            MST_Expr* expr = AllocMST_Expr(2);
            if (!list2.size() || list2.back().index() != 1 || list.size() <= j+1 || list[j+1].index() != 1) {
              cout << "parse error" << endl;
              if (Mode) {
                Error = 1;
                return {};
              } else {
                exit(-1);
              }
            }
            expr->Operands[0] = get<MST_Object*>(list2.back());
            if (setn) {
              MST_Expr* expr2 = AllocMST_Expr(2);
              expr2->Operator = opms;
              expr2->Operands[0] = CopyMST_Object(get<MST_Object*>(list2.back()));
              expr2->Operands[1] = get<MST_Object*>(list[j+1]);
              expr->Operands[1] = (MST_Object*)expr2;
              expr->Operator = mode ? MST_Set : MST_Bind;
            } else {
              expr->Operator = opms;
              expr->Operands[1] = get<MST_Object*>(list[j+1]);
            }
            list2.pop_back();
            list2.push_back((MST_Object*)expr);
            j++;
            continue;
          }
        }
        list2.push_back(list[j]);
      }
      list = list2;
    }
  }
  list2 = {};
  for (int i = 0; i < list.size(); i++) {
    if (list[i].index() == 0) {
      int idop = get<MSTP_TokenInfo*>(list[i])->OprtID;
      if (idop == MSTP_Comma) {
        continue;
      }
      if (idop == MSTP_Semicolon) {
        if (!mode) {
          MST_Str* str = AllocMST_Str(6);
          strcpy(str->Data, "waitev");
          MST_Object* ref = (MST_Object*)malloc(sizeof(MST_Object));
          ref->Type = MST_SymbolReference;
          ref->Ptr = str;
          MST_Expr* expr = AllocMST_Expr(1);
          expr->Operator = MST_Call;
          expr->Operands[0] = ref;
          list2.push_back((MST_Object*)expr);
          continue;
        }
        if (CwkCnt) {
          MST_Expr* expr = AllocMST_Expr(2);
          expr->Operator = MST_Set;
          expr->Operands[0] = CopyMST_Object(CwkCnt);
          expr->Operands[1] = AllocMST_Val(32);
          *((int*)expr->Operands[1]->Ptr) = nState+1;
          list2.push_back((MST_Object*)expr);
          CLFlag |= 1;
          continue;
        }
      }
      if (idop == MSTP_ColonSemicolon) {
        CLFlag |= 1;
        continue;
      }
    }
    list2.push_back(list[i]);
  }
  return list2;
}


vector<MST_Object*> MSTP_Parse(char* src) {
  return mstp->Parse(src);
}

vector<MST_Object*> MST_Parser::Read() {
  char buff[0xffff];
  int n = 0;
  int ll = 0;
  int npar = 0;
  int nbr = 0;
  int nest = 0;
  int sem = 0;
  int c = 0;
  while(1) {
    if (n > 0xfffe) {
      if (Mode) {
        return {};
      } else {
        exit(-1);
      }
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
        if (!npar) {
          cout << "unbalanced parentheses" << endl;
          if (Mode) {
            Error = 1;
            return {};
          } else {
            exit(-1);
          }
        }
        npar--;
        break;
      case '[':
        nbr++;
        break;
      case ']':
      if (!nbr) {
          cout << "unbalanced blackets" << endl;
          if (Mode) {
            Error = 1;
            return {};
          } else {
            exit(-1);
          }
        }
        nbr--;
        break;
    }
    if (c == '\n') {
      if ((!ll || !nest) && !npar && !nbr && !sem) {
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
  return Parse(buff);
}

vector<MST_Object*> MSTP_Read() {
  return mstp->Read();
}

int MSTP_SetMode(int m) {
  return mstp->SetMode(m);
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
