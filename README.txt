System Verilogのコードを生成したり、回路シミュレーションができるインタプリタです。
testip.exeを実行するとインタプリタが起動します。
コメントアウトは未実装なので各行の//より前の文字列を入力し、エンターを押してください
例:
CLK = in[] //ビット幅1の入力信号"CLK"を追加します。
LEDR = out[10] //ビット幅10の出力信号"LEDR"を追加します
printsv() //現在のSystem Verilogコードを表示します

at (pos CLK): //CLK信号の立ち上がりエッジに次の処理を実行します
  LEDR = ~LEDR //LEDRを反転する(タブまたはスペース二つでインデントしてください)
  
printsv()
clk = {$CLK} //リスト"clk"を生成し、信号"CLK"の値を格納する
led = {$LEDR}

for (i 100):　//次の処理を100回繰り返します
  CLK $= $!CLK; //CLKの信号を反転し、信号の変化によって発生するイベントを処理します
  clk.push($CLK) //CLKの現在の値を配列に追加します
  led.push($LEDR)

tchart(clk, led) //リストclk、ledを元にタイミングチャートをsvgファイルで生成します(./timingchart.svg)

TO DO
・リスト要素への代入
・多重リスト
・メモリリークの調査
