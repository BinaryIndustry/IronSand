#ifndef HASHTABLE_CPP
#define HASHTABLE_CPP

#include <iostream>
#include <vector>
#include <stdint.h>
#include <string.h>

using namespace std;

typedef struct HashTableItem{
  uint32_t Sum;
  uint32_t Hash;

  uint8_t* Key;
  int KeyLen;

  void* Item;
} HashTableItem;

#define MAX_SIZE_HASHTABLE 0xffffff
#define BUFF_SIZE_HASHTABLE 0xff

template<typename T>
class HashTable {
private:
  vector<HashTableItem> Table;

  int Size;

  int nItems;
  int ResizeLine;

  int MaxKeyLen;

public:
  HashTable(int s = 8) {
    Size = (1 << s)-1;
    Table.resize(Size+1, {0, 0, NULL, 0, NULL});
    nItems = 0;
    ResizeLine = Size >> 2;
    MaxKeyLen = 0;
  }

  ~HashTable() {
    for (int i = 0; i < Table.size(); i++) {
      if (Table[i].Key) {
        delete Table[i].Key;
        delete (T*)Table[i].Item;
      }
    }
  }

  int GetMaxKeyLen() {
    return MaxKeyLen;
  }

  uint32_t GenHash(uint8_t* key, int len) {
    uint32_t hash = 0;
    for (int i = 0; i < len; i++) {
      hash += (hash << 2) + key[i];
    }
    return hash;
  }

  uint32_t Sum(uint8_t* key, int len) {
    uint32_t sum = 0;
    for (int i = 0; i < len; i++) {
      sum += key[i];
    }
    return sum;
  }

  uint32_t TraceHash(uint8_t* key, int len, uint32_t* hash, uint32_t* sum) {
    hash[0] = key[0];
    sum[0] = key[0];
    for (int i = 1; i < len; i++) {
      hash[i] = (hash[i-1] << 2) + hash[i-1] + key[i];
      sum[i] = sum[i-1] + key[i];
    }
    return hash[len-1];
  }

  int Resize() {
    if (Size > MAX_SIZE_HASHTABLE) {
      return -1;
    }

    int prevsize = Size;

    Size <<= 2;
    Size |= 3;

    ResizeLine = Size >> 2;

    vector<HashTableItem> old = Table;

    Table.clear();
    Table.resize(Size+1, {0, 0, NULL, 0, NULL});


    for (int i = 0; i < prevsize; i++) {
      if (old[i].Key) {
        uint32_t base = old[i].Hash & Size;
        int j;
        for (j = base; j < base + Size; j++) {
          if (!Table[j].Key) {
            Table[j] = old[i];
            break;
          }
        }
        if (j == base + Size) {
          cout << "HashTable: Could not find free slot" << endl;
          return -1;
        }
      }
    }

    return 0;
  }

  T& Get(uint8_t* key, int len) {
    uint32_t s = Sum(key, len);
    uint32_t h = GenHash(key, len);


    if (nItems > ResizeLine) {
      cout << "Hashtable: Could not expand" << endl;
      if (Resize()) exit(-1);
    }

    for (int i = 0; i < Size; i++) {
      int j = (h + i) & Size;
      if (!Table[j].Key) {
        Table[j].Sum = s;
        Table[j].Hash = h;
        Table[j].Key = new uint8_t[len];
        Table[j].KeyLen = len;
        for (int i = 0; i < len; i++) {
          Table[j].Key[i] = key[i];
        }
        Table[j].Item = new T;
        nItems++;
        if (len > MaxKeyLen) MaxKeyLen = len;
        return *(T*)Table[j].Item;
      }
      if (Table[j].Sum == s && Table[j].Hash == h && len == Table[j].KeyLen
        && !memcmp(key, Table[j].Key, len)) {
        return *(T*)Table[j].Item;
      }
    }
    cout << "HashTable: Could not find free slot" << endl;
    exit(-1);
  }

  T& Get(string key) {
    return Get((uint8_t*)key.c_str(), key.size());
  }

  T* Find(uint8_t* key, int len) {
    return Find(key, len, GenHash(key, len), Sum(key, len));
  }

  T* Find(string key) {
    return Find((uint8_t*)key.c_str(), key.size());
  }

  T* Find(uint8_t* key, int len, uint32_t hash, uint32_t sum) {
    for (int i = 0; i < Size; i++) {
      int j = (hash + i) & Size;
      if (!Table[j].Key) {
        return NULL;
      }
      if (Table[j].Sum == sum && Table[j].Hash == hash && len == Table[j].KeyLen
        && !memcmp(key, Table[j].Key, len)) {
        return (T*)Table[j].Item;
      }
    }
    return NULL;
  }

  T Set(string key, T& val) {
    return Get(key) = val;
  }

  struct keyval {
    string key;
    T val;
  };

  int Set(vector<struct keyval> arg) {
    for (int i = 0; i < arg.size(); i++) {
      Get(arg[i].key) = arg[i].val;
    }
    return arg.size();
  }

  int SearchBack(uint8_t* key, int len = 0, T** buff = NULL) {
    uint32_t buff_hash[BUFF_SIZE_HASHTABLE], buff_sum[BUFF_SIZE_HASHTABLE];

    if (len <= 0 || len > MaxKeyLen) len = MaxKeyLen;

    uint32_t* hash;
    uint32_t* sum;

    if (len > BUFF_SIZE_HASHTABLE) {
      hash = new uint32_t[len];
      sum = new uint32_t[len];
    } else {
      hash = buff_hash;
      sum = buff_sum;
    }

    TraceHash(key, len, hash, sum);

    int ret = 0;

    if (buff) {
      for (int i = 0; i < len; i++) {
        if (buff[i] = Find(key, i+1, hash[i], sum[i])) {
          ret = i + 1;
        }
      }
    } else {
      for (int i = len; i; i--) {
        if (Find(key, i, hash[i-1], sum[i-1])){
          ret = i;
          break;
        }
      }
    }

    if (hash != buff_hash) {
      delete hash;
      delete sum;
    }
    return ret;
  }

  int SearchBack(string key, T** buff = NULL) {
    return SearchBack((uint8_t*)key.c_str(), key.size(), buff);
  }

};


#endif
