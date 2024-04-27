System Verilogのコードを生成したり、回路シミュレーションができるインタプリタです。
testip.exeを実行するとインタプリタが起動します。
例:
CLK = in[] //ビット幅1の入力信号"CLK"を追加します。
LEDR = out[10] //ビット幅10の出力信号"LEDR"を追加します
printsv() //現在のSystem Verilogコードを表示します
cnt = [32] //32ビットのカウンタを生成します
at (pos CLK):
  if (cnt == 50000000):
    cnt = 0 //cntが50000000ならcntをリセット
    LEDR = ~LEDR //LEDRのビットを反転
  else:
    cnt = cnt + 1 //cntが50000000以外ならインクリメント
