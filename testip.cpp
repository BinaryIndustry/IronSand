#include "mightstone.h"
#include "mstparser.h"
#include <iostream>
#include <string>
#include <stdlib.h>
#include <fstream>

int quit = 0;

MST_Object* QuitInterPreter(int nargs, MST_Object** args) {
  quit = 1;
  return NULL;
}

MST_Object* WriteSV(int nargs, MST_Object** args) {
  ofstream ofs("main.sv");
  if (!ofs) {
    cout << "failed to create file" << endl;
    exit(-1);
  }
  ofs << MST_SVCode();
  return NULL;
}

MST_Object* PrintSV(int nargs, MST_Object** args) {
  cout << MST_SVCode();
  return NULL;
}

MST_Object* WaitEv(int nargs, MST_Object** args) {
  MST_WaitTask();
  return NULL;
}

MST_Object* Print(int nargs, MST_Object** args) {
  if (nargs && args[0]) {
    if (args[0]->Type == MST_Value) {
      cout << GetIntMST_Obj(args[0]) << endl;
    }
  }
  return NULL;
}

int main() {
  AddMST_ExFunc(string("quit"), QuitInterPreter);
  AddMST_ExFunc(string("writesv"), WriteSV);
  AddMST_ExFunc(string("printsv"), PrintSV);
  AddMST_ExFunc(string("waitev"), WaitEv);
  AddMST_ExFunc(string("print"), Print);

  vector<MST_Object*> obj;
  while(!quit) {
    obj = MSTP_Read();
    for (int i = 0; i < obj.size(); i++) {
      if (obj[i]) {
        if (obj[i]->Type == MST_Expression) {
          MST_Expr* expr = (MST_Expr*)obj[i];
          MST_Object* ret = EvalMST_Expr(expr, 0);
          if (ret && expr->Operator != MST_Bind) {
            if (ret->Type == MST_Value) {
              MST_Val* val = (MST_Val*)ret;
              if (!val->nDim && val->ItemWidth <= 32) {
                cout << GetIntMST_Obj((MST_Object*)val) << endl;
              }
            }
          }
          if (ret) {
            FreeMST_Object(ret);
          }
        } else if (obj[i]->Type == MST_Value) {
          MST_Val* val = (MST_Val*)obj[i];
          if (!val->nDim && val->ItemWidth <= 32) {
            cout << GetIntMST_Obj((MST_Object*)val) << endl;
          }
        }
        FreeMST_Object(obj[i]);
      }
    }
  }

  ofstream ofs("main.sv");
  if (!ofs) {
    cout << "failed to create file" << endl;
    exit(-1);
  }
  ofs << MST_SVCode();

  return 0;
}
