System Verilogのコードを生成したり、回路シミュレーションができるインタプリタです。</br>
testip.exeを実行するとインタプリタが起動します。</br>
例:</br>
CLK = in[] //ビット幅1の入力信号"CLK"を追加します。</br>
LEDR = out[10] //ビット幅10の出力信号"LEDR"を追加します</br>
printsv() //現在のSystem Verilogコードを表示します</br>
cnt = [32] //32ビットのカウンタを生成します</br>
at (pos CLK):</br>
  if (cnt == 50000000):</br>
    cnt = 0 //cntが50000000ならcntをリセット</br>
    LEDR = ~LEDR //LEDRのビットを反転</br>
  else:</br>
    cnt = cnt + 1 //cntが50000000以外ならインクリメント</br>
