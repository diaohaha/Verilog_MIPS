//-------------------------------------------------------
// mips.v
// author:gaoda,tanshuai
// Model of subset of MIPS 
//-------------------------------------------------------

module top #(parameter WIDTH = 32, REGBITS = 5)();

   reg                 clk;
   reg                 reset;
   wire                memread, memwrite;
   wire    [WIDTH-1:0] adr, writedata;
   wire    [WIDTH-1:0] memdata;

   mips #(WIDTH,REGBITS) dut(clk, reset, memdata, memread, memwrite, adr, writedata);
   exmemory #(WIDTH) exmem(clk, memwrite, adr, writedata, memdata);

   initial
      begin
         reset <= 1; # 22; reset <= 0;
      end

   always
      begin
         clk <= 1; # 5; clk <= 0; # 5;
      end

   always@(negedge clk)
      begin
         if(memread)
            $display("read  %b at address %b",memdata,adr);
         if(memwrite)
            $display("write %b at address %b",writedata,adr);
      end
endmodule

//mem
module exmemory #(parameter WIDTH = 32)
                 (clk, memwrite, adr, writedata, memdata);

   input                  clk;
   input                  memwrite;
   input      [WIDTH-1:0] adr, writedata;
   output reg [WIDTH-1:0] memdata;

   reg  [31:0] RAM [63:0];
   wire [31:0] word;

   initial
      begin
         $readmemh("addu.dat",RAM);
      end

   always @(posedge clk)
      if(memwrite) 
             RAM[adr] <= writedata;

   assign word = RAM[adr];
   always @(*)
         memdata <= word;
    
endmodule


//cpu
module mips #(parameter WIDTH = 32, REGBITS = 5)
             (input              clk, reset, 
              input  [WIDTH-1:0] memdata, 
              output             memread, memwrite,
              output [WIDTH-1:0] adr, writedata);
   

   wire [31:0] instr;
   wire        zero, alusrca, memtoreg, iord, pcen, regwrite, regdst,upzero;
   wire [1:0]  aluop,pcsource,alusrcb;
   wire        irwrite;
   wire [3:0]  alucont;
   wire [2:0]  pccond;

   controller  cont(clk,//in 
                    reset,
                    instr[31:26],
                    zero,
                    pcwritecond2,
                    memread,//out
                    memwrite, 
                    alusrca,
                    memtoreg,
                    iord,
                    pcen,
                    regwrite,
                    regdst,
                    pcsource,
                    pccond,
                    alusrcb,
                    aluop,
                    irwrite);
   alucontrol  ac(aluop,
                  instr[31:26],
                  instr[5:0],
                  alucont);
   datapath    #(WIDTH, REGBITS) 
               dp(clk,
                  reset,
                  memdata,
                  alusrca,
                  memtoreg,
                  iord,
                  pcen,
                  regwrite,
                  regdst,
                  pcsource,
                  alusrcb,
                  irwrite,
                  pccond,
                  alucont,
                  zero,
                  upzero,
                  pcwritecond2,
                  instr,
                  adr,
                  writedata);
endmodule

module controller(input            clk,
                  input            reset, 
                  input      [5:0] op, 
                  input            zero,
                  input            pcwritecond2, 
                  output reg       memread,
                  output reg       memwrite,
                  output reg       alusrca,
                  output reg       memtoreg,
                  output reg       iord, 
                  output           pcen, 
                  output reg       regwrite,
                  output reg       regdst, 
                  output reg [1:0] pcsource,
                  output reg [2:0] pccond,
                  output reg [1:0] alusrcb,
                  output reg [1:0] aluop, 
                  output reg       irwrite);

   parameter   FETCH   =  4'b0001;
   parameter   DECODE  =  4'b0101;
   parameter   MEMADR  =  4'b0110;
   parameter   LWRD    =  4'b0111;
   parameter   LWWR    =  4'b1000;
   parameter   SWWR    =  4'b1001;
   parameter   RTYPEEX =  4'b1010;
   parameter   RTYPEWR =  4'b1011;
   parameter   BEQEX   =  4'b1100;
   parameter   JEX     =  4'b1101;
   parameter   ITYPEEX =  4'b1111;
   parameter   ITYPEWR =  4'b1110;
   parameter   ENDEX   =  4'b0000;
   
   //i-Type
   parameter   LW      =  6'b100011;
   parameter   SW      =  6'b101011;
   parameter   BLTZ    =  6'b000001;
   parameter   BGEZ    =  6'b000001;
   parameter   BLEZ    =  6'b000110;
   parameter   BGTZ    =  6'b000111;
   parameter   BNE     =  6'b000101;
   parameter   ADDI    =  6'b001000;
   parameter   ADDIU   =  6'b001001;
   parameter   ANDI    =  6'b001000;
   parameter   BEQ     =  6'b000100;
   parameter   ORI     =  6'b001101;
   parameter   XORI    =  6'b001110;
   parameter   SLTI    =  6'b001010;
   parameter   SLTIU   =  6'b001011;
   
   //J-Type
   parameter   J       =  6'b000010;
   
   //R-Type
   parameter   RTYPE   =  6'b0;
   parameter   ADD     =  6'b0;
   parameter   ADDU    =  6'b0;
   parameter   SUB     =  6'b0;
   parameter   SUBU    =  6'b0;
   parameter   AND     =  6'b0;
   parameter   OR      =  6'b0;
   parameter   XOR     =  6'b0;
   parameter   SLT     =  6'b0;
   parameter   SLTU    =  6'b0;
   parameter   SLLV    =  6'b0;
   parameter   SRLV    =  6'b0;
   parameter   SRAV    =  6'b0;

   parameter   END     =  6'b111111;
   reg [3:0] state, nextstate;
   reg       pcwrite, pcwritecond;

   //????
   always @(posedge clk)
      if(reset) state <= FETCH;
      else state <= nextstate;


   always @(*)
      begin
         case(state)
            FETCH:  nextstate <= DECODE;
            DECODE:  case(op)
                        END:     nextstate <= ENDEX;
                        LW:      nextstate <= MEMADR;
                        SW:      nextstate <= MEMADR;
                        RTYPE:   nextstate <= RTYPEEX;
                        ADD:     nextstate <= RTYPEEX;
                        ADDU:    nextstate <= RTYPEEX;
                        SUB:     nextstate <= RTYPEEX;
                        SUBU:    nextstate <= RTYPEEX;
                        OR:      nextstate <= RTYPEEX;
                        XOR:     nextstate <= RTYPEEX;
                        SLT:     nextstate <= RTYPEEX;
                        SLTU:    nextstate <= RTYPEEX;
                        SLLV:    nextstate <= RTYPEEX;
                        SRLV:    nextstate <= RTYPEEX;
                        SRAV:    nextstate <= RTYPEEX; 
                        BEQ:     nextstate <= BEQEX;
                        BLTZ:    nextstate <= BEQEX;
                        BGEZ:    nextstate <= BEQEX;
                        BLEZ:    nextstate <= BEQEX;
                        BGTZ:    nextstate <= BEQEX;
                        BNE:     nextstate <= BEQEX;
                        J:       nextstate <= JEX;
                        ADDI:    nextstate <= ITYPEEX;
                        ADDIU:   nextstate <= ITYPEEX;
                        ANDI:    nextstate <= ITYPEEX;
                        ORI:     nextstate <= ITYPEEX;
                        XORI:    nextstate <= ITYPEEX;
                        SLTI:    nextstate <= ITYPEEX;
                        SLTIU:   nextstate <= ITYPEEX;
                        default: nextstate <= FETCH;
                     endcase
            MEMADR:  case(op)
                        LW:      nextstate <= LWRD;
                        SW:      nextstate <= SWWR;
                        default: nextstate <= FETCH;
                     endcase
            LWRD:    nextstate <= LWWR;
            LWWR:    nextstate <= FETCH;
            SWWR:    nextstate <= FETCH;
            RTYPEEX: nextstate <= RTYPEWR;
            RTYPEWR: nextstate <= FETCH;
            ITYPEEX: nextstate <= ITYPEWR;
            ITYPEWR: nextstate <= FETCH;
            BEQEX:   nextstate <= FETCH;
            JEX:     nextstate <= FETCH;
            ENDEX:   $display("programe over");
            default: nextstate <= FETCH;
         endcase
      end
   
  
   always @(*)
      begin
            irwrite <= 0;
            pcwrite <= 0; pcwritecond <= 0;
            regwrite <= 0; regdst <= 0;
            memread <= 0; memwrite <= 0;
            alusrca <= 0; alusrcb <= 2'b00; aluop <= 2'b00;
            pcsource <= 2'b00;
            iord <= 0; memtoreg <= 0;            
            
            case(state)
               FETCH:
                  begin
                     memread <= 1; 
                     irwrite <= 1; 
                     alusrcb <= 2'b01; 
                     pcwrite <= 1;
                  end
               DECODE: alusrcb <= 2'b01;
               MEMADR:
                  begin
                     alusrca <= 1;
                     alusrcb <= 2'b11;
                  end
               LWRD:
                  begin
                     memread <= 1;
                     iord    <= 1;
                  end
               LWWR:
                  begin
                     regwrite <= 1;
                     memtoreg <= 1;
                  end
               SWWR:
                  begin
                     memwrite <= 1;
                     iord     <= 1;
                  end
               RTYPEEX:
                  begin
                     alusrca <= 1;
                     aluop   <= 2'b10;
                  end
               RTYPEWR:
                  begin
                     regdst   <= 1;
                     regwrite <= 1;
                  end
               ITYPEEX:
                  begin
                     alusrca <= 1;
                     alusrcb <= 2'b11;
                     aluop   <= 2'b11;
                  end 
               ITYPEWR:
                  begin
                     regdst   <= 0;
                     regwrite <= 1;
                  end   
               BEQEX:
                  begin
                     alusrca     <= 1;
                     aluop       <= 2'b01;
                     case(op)
                        BLTZ: pccond <= 3'b000;
                        BGEZ: pccond <= 3'b001;
                        BLEZ: pccond <= 3'b010;
                        BGTZ: pccond <= 3'b011;
                        BNE:  pccond <= 3'b100;
                        BEQ:  pccond <= 3'b101;
                     endcase
                     pcwritecond <= 1;
                     pcsource    <= 2'b01;
                  end  
               JEX:
                  begin
                     pcwrite  <= 1;
                     pcsource <= 2'b10;
                  end
         endcase
      end
   assign pcen = pcwrite | (pcwritecond & pcwritecond2); //     
endmodule

module alucontrol(input      [1:0] aluop, 
                  input      [5:0] op,
                  input      [5:0] funct, 
                  output reg [3:0] alucont);

   always @(*)
      case(aluop)
         2'b00: alucont <= 4'b1011;
         2'b01: alucont <= 4'b0111;
         2'b11: case(op)
                     6'b001000: alucont <= 4'b1011;//addi
                     6'b001001: alucont <= 4'b0110;//sltiu
                     6'b001100: alucont <= 4'b0000;//andi
                     6'b001101: alucont <= 4'b0001;//ori
                     6'b001110: alucont <= 4'b0010;//xori
                     6'b001010: alucont <= 4'b1000;//slti
                     6'b001011: alucont <= 4'b0100;//addiu
                     default:   alucont <= 4'b1111;
                endcase     
         2'b10: case(funct)       // R-Type instructions
                     6'b100000: alucont <= 4'b1011;//
                     6'b100001: alucont <= 4'b0100;
                     6'b100010: alucont <= 4'b0111;
                     6'b100011: alucont <= 4'b0101;
                     6'b100100: alucont <= 4'b0000;
                     6'b100101: alucont <= 4'b0001;
                     6'b100110: alucont <= 4'b0010;
                     6'b100111: alucont <= 4'b0011;
                     6'b101010: alucont <= 4'b1000;
                     6'b101011: alucont <= 4'b0110;
                     6'b000111: alucont <= 4'b1100;//srav
                     6'b000100: alucont <= 4'b1001;//sllv
                     6'b000110: alucont <= 4'b1010;//srlv
                     default:   alucont <= 4'b1111;
                  endcase
      endcase
endmodule

module datapath #(parameter WIDTH = 32, REGBITS = 5)
                 (input              clk,
                  input              reset, 
                  input  [WIDTH-1:0] memdata, 
                  input              alusrca,
                  input              memtoreg, 
                  input              iord,
                  input              pcen,
                  input              regwrite,
                  input              regdst,
                  input  [1:0]       pcsource,
                  input  [1:0]       alusrcb,
                  input              irwrite,
                  input  [2:0]       pccond, 
                  input  [3:0]       alucont, 
                  output             zero,
                  output             upzero,
                  output             pcwritecond2,
                  output [31:0]      instr, 
                  output [WIDTH-1:0] adr,
                  output [WIDTH-1:0] writedata);

   parameter CONST_ZERO =  32'b0;
   parameter CONST_ONE  =  32'b1;

   wire [REGBITS-1:0] ra1, ra2, wa;
   wire [WIDTH-1:0]   pc, nextpc, md, rd1, rd2, wd, a, src1, src2, aluresult, aluout, JUMP_ADR, BEQ_ADR, extend;
   wire               beg,bne,bltz,bgez,blez,bgtz;
   
   assign ra1 = instr[REGBITS+20:21];
   assign ra2 = instr[REGBITS+15:16];
   mux2       #(REGBITS) regmux(instr[REGBITS+15:16], instr[REGBITS+10:11], regdst, wa);
   flopen     #(WIDTH)      ir0(clk, irwrite, memdata[31:0], instr[31:0]);
   extend     #(WIDTH) extend16(instr[15:0],extend);
   assign JUMP_ADR = {6'b000000,instr[25:0]};
   assign BEQ_ADR  = {16'b0000000000000000,instr[15:0]};
   // datapath
   flopenr    #(WIDTH)  pcreg(clk, reset, pcen, nextpc, pc);
   flop       #(WIDTH)  mdr(clk, memdata, md);
   flop       #(WIDTH)  areg(clk, rd1, a);  
   flop       #(WIDTH)  wrd(clk, rd2, writedata);
   flop       #(WIDTH)  res(clk, aluresult, aluout);
   mux2       #(WIDTH)  adrmux(pc, aluout, iord, adr);
   mux2       #(WIDTH)  src1mux(pc, a, alusrca, src1);
   mux4       #(WIDTH)  src2mux(writedata, CONST_ONE, instr[WIDTH-1:0], extend, alusrcb, src2);
   mux4       #(WIDTH)  pcmux(aluresult, BEQ_ADR, JUMP_ADR, CONST_ZERO, pcsource, nextpc);
   mux2       #(WIDTH)  wdmux(aluout, md, memtoreg, wd);
   regfile    #(WIDTH,REGBITS) rf(clk, regwrite, ra1, ra2, wa, wd, rd1, rd2);
   alu        #(WIDTH) alunit(src1, src2, alucont, aluresult);
   zerodetect #(WIDTH) zd(aluresult, zero);
   updetect   #(WIDTH) aaa(aluresult, upzero);
   tiaozhuan  #(WIDTH) bbb(zero,upzero,beq,bne,bltz,bgez,blez,bgtz);
   mux6       #(WIDTH) ddd(bltz,bgez,blez,bgtz,bne,beq, pccond, pcwritecond2);
   
endmodule 

module alu #(parameter WIDTH = 32)
            (input      [WIDTH-1:0] a, b, 
             input      [3:0]       alucont, 
             output reg [WIDTH-1:0] result);

   wire     [WIDTH-1:0] sra;
   parameter temp = 32'b1;
   assign sra = a[WIDTH-1] ? ((a>>b)+(~(temp>>b))):(a>>b);
   always@(*)
      case(alucont[3:0])
         4'b0000: result <= a & b;//and
         4'b0001: result <= a | b;//or
         4'b0010: result <= ~(a&b)&(a|b);//xor
         4'b0011: result <= (~a)&(~b);//nor
         4'b0100: result <= a + b;//addu
         4'b0101: result <= a - b;//subu
         4'b0110: result <= (a > b) ? 1:0;//sltu
         4'b0111: result <= $signed(a) - $signed(b);//sub
         4'b1000: result <= ($signed(a) > $signed(b)) ? 1:0;//slt
         4'b1001: result <= a << b;//sll
         4'b1010: result <= a >> b;//srl
         4'b1100: result <= sra;//sra
         4'b1011: result <= $signed(a) + $signed(b);//add
      endcase
endmodule

module regfile #(parameter WIDTH = 32, REGBITS = 5)
                (input                clk, 
                 input                regwrite, 
                 input  [REGBITS-1:0] ra1, ra2, wa, 
                 input  [WIDTH-1:0]   wd, 
                 output [WIDTH-1:0]   rd1, rd2);
                 
   reg  [WIDTH-1:0] RAM [(1<<REGBITS)-1:0];//The definition of a register
   
   always @(posedge clk)
      if (regwrite) RAM[wa] <= wd;	
   
   initial
      RAM[5'b0] = 32'b00000000000000000000000000000000;//Number 0 reg is const zero...
   
   assign rd1 = ra1 ? RAM[ra1] : 0;
   assign rd2 = ra2 ? RAM[ra2] : 0;
endmodule

module zerodetect #(parameter WIDTH = 32)
                   (input [WIDTH-1:0] a, 
                    output            y);

   assign y = (a==0);
endmodule	

module updetect #(parameter WIDTH = 32)
                   (input [WIDTH-1:0] a, 
                    output            y);

   assign y = (a>0);
endmodule

module flop #(parameter WIDTH = 32)
             (input                  clk, 
              input      [WIDTH-1:0] d, 
              output reg [WIDTH-1:0] q);

   always @(posedge clk)
      q <= d;
endmodule

module flopen #(parameter WIDTH = 32)
               (input                  clk, en,
                input      [WIDTH-1:0] d, 
                output reg [WIDTH-1:0] q);

   always @(posedge clk)
      if (en) q <= d;
endmodule

module flopenr #(parameter WIDTH = 32)
                (input                  clk, reset, en,
                 input      [WIDTH-1:0] d, 
                 output reg [WIDTH-1:0] q);
 
   always @(posedge clk)
      if      (reset) q <= 0;
      else if (en)    q <= d;
endmodule

module mux2 #(parameter WIDTH = 32)
             (input  [WIDTH-1:0] d0, d1, 
              input              s, 
              output [WIDTH-1:0] y);

   assign y = s ? d1 : d0; 
endmodule

module mux4 #(parameter WIDTH = 32)
             (input      [WIDTH-1:0] d0, d1, d2, d3,
              input      [1:0]       s, 
              output reg [WIDTH-1:0] y);

   always @(*)
      case(s)
         2'b00: y <= d0;
         2'b01: y <= d1;
         2'b10: y <= d2;
         2'b11: y <= d3;
      endcase
endmodule

module mux6 #(parameter WIDTH = 32)
             (input                  d0, d1, d2, d3, d4, d5,
              input      [2:0]       s, 
              output reg             y);

   always @(*)
      case(s)
         3'b000: y <= d0;
         3'b001: y <= d1;
         3'b010: y <= d2;
         3'b011: y <= d3;
         3'b100: y <= d4;
         3'b101: y <= d5;
      endcase
endmodule

module extend #(parameter WIDTH=32)
             (input [15:0]a,
              output [WIDTH-1:0]extend);
   assign extend = {16'b0,a[15:0]};
endmodule

module tiaozhuan #(parameter WIDTH = 32)
                  (input zero,upzero,
                   output beq,bne,bltz,bgez,blez,bgtz);
     assign beq  = zero;
     assign bltz = ~upzero & (~zero);
     assign bgez = upzero | zero;
     assign blez = ~upzero;
     assign bgtz = upzero;
     assign bne =  ~zero;
endmodule//
