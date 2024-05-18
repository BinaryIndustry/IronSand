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

int main(int argc, char* argv[]) {
  AddMST_ExFunc(string("quit"), QuitInterPreter);
  AddMST_ExFunc(string("writesv"), WriteSV);
  AddMST_ExFunc(string("printsv"), PrintSV);
  AddMST_ExFunc(string("waitev"), WaitEv);
  AddMST_ExFunc(string("print"), Print);
  AddMST_ExFunc(string("tchart"), TimingChart);

  if (argc > 1) {
    for (int i = 0; i < argc-1; i++) {
      FILE* fp = fopen(argv[i+1], "r");
      if (!fp) {
        cout << "could not open " << string(argv[i+1]) << endl;
        exit(-1);
      }
      static char buff[0xffff];
      int n = fread(buff, 1, 0xffff, fp);
      if (n > 0xfffe || n < 0) {
        exit(-1);
      }
      buff[n] = 0;
      vector<MST_Object*> obj;
      obj = MSTP_Parse(buff);
      for (int j = 0; j < obj.size(); j++) {
        if (obj[j]->Type == MST_Expression) {
          MST_Object* ret = EvalMST_Expr((MST_Expr*)obj[j], 0);
          if (ret) {
            FreeMST_Object(ret);
          }
        } else if (obj[j]) {
          FreeMST_Object(obj[j]);
        }
      }
    }
    ofstream ofs("main.sv");
    if (!ofs) {
      cout << "failed to create file" << endl;
      exit(-1);
    }
    ofs << MST_SVCode();
  } else {
    MST_SetMode(1);
    MSTP_SetMode(1);

    vector<MST_Object*> obj;
    while(!quit) {
      obj = MSTP_Read();
      for (int i = 0; i < obj.size(); i++) {
        if (obj[i]) {
          if (obj[i]->Type == MST_Expression) {
            MST_Expr* expr = (MST_Expr*)obj[i];
            MST_Object* ret = EvalMST_Expr(expr, 0);
            if (ret && expr->Operator != MST_Bind) {
              if (ret && ret->Type == MST_Value) {
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
  }

  return 0;
}
