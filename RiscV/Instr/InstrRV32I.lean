/-
Copyright (c) 2022 RISC Zero. All rights reserved.
-/

import RiscV.Instr.Types
import RiscV.Mem
import RiscV.Monad
import RiscV.Reg

namespace RiscV.Instr.InstrRV32I

open Types
open Mem
open Monad
open Reg

/-
Volume I: RISC-V Unprivileged ISA V20191213
RV32I Base Instruction Set

funct7          rs2   rs1   funct3          rd    opcode    R-type
imm[11:0]             rs1   funct3          rd    opcode    I-type
imm[11:5]       rs2   rs1   funct3     imm[4:0]   opcode    S-type
imm[12|10:5]    rs2   rs1   funct3  imm[4:1|11]   opcode    B-type
imm[31:12]                                  rd    opcode    U-type
imm[20|10:1|11|19:12]                       rd    opcode    J-type

imm[31:12]                                  rd    0110111   LUI
imm[31:12]                                  rd    0010111   AUIPC
imm[20|10:1|11|19:12]                       rd    1101111   JAL
imm[11:0]             rs1   000             rd    1100111   JALR
imm[12|10:5]    rs2   rs1   000     imm[4:1|11]   1100011   BEQ
imm[12|10:5]    rs2   rs1   001     imm[4:1|11]   1100011   BNE
imm[12|10:5]    rs2   rs1   100     imm[4:1|11]   1100011   BLT
imm[12|10:5]    rs2   rs1   101     imm[4:1|11]   1100011   BGE
imm[12|10:5]    rs2   rs1   110     imm[4:1|11]   1100011   BLTU
imm[12|10:5]    rs2   rs1   111     imm[4:1|11]   1100011   BGEU
imm[11:0]             rs1   000             rd    0000011   LB
imm[11:0]             rs1   001             rd    0000011   LH
imm[11:0]             rs1   010             rd    0000011   LW
imm[11:0]             rs1   100             rd    0000011   LBU
imm[11:0]             rs1   101             rd    0000011   LHU
imm[11:5]       rs2   rs1   000       imm[4:0]    0100011   SB
imm[11:5]       rs2   rs1   001       imm[4:0]    0100011   SH
imm[11:5]       rs2   rs1   010       imm[4:0]    0100011   SW
imm[11:0]             rs1   000             rd    0010011   ADDI
imm[11:0]             rs1   010             rd    0010011   SLTI
imm[11:0]             rs1   011             rd    0010011   SLTIU
imm[11:0]             rs1   100             rd    0010011   XORI
imm[11:0]             rs1   110             rd    0010011   ORI
imm[11:0]             rs1   111             rd    0010011   ANDI
0000000       shamt   rs1   001             rd    0010011   SLLI
0000000       shamt   rs1   101             rd    0010011   SRLI
0100000       shamt   rs1   101             rd    0010011   SRAI
0000000         rs2   rs1   000             rd    0110011   ADD
0100000         rs2   rs1   000             rd    0110011   SUB
0000000         rs2   rs1   001             rd    0110011   SLL
0000000         rs2   rs1   010             rd    0110011   SLT
0000000         rs2   rs1   011             rd    0110011   SLTU
0000000         rs2   rs1   100             rd    0110011   XOR
0000000         rs2   rs1   101             rd    0110011   SRL
0100000         rs2   rs1   101             rd    0110011   SRA
0000000         rs2   rs1   110             rd    0110011   OR
0000000         rs2   rs1   111             rd    0110011   AND
fm    pred     succ   rs1   000             rd    0001111   FENCE
000000000000    00000       000          00000    1110011   ECALL
000000000001    00000       000          00000    1110011   EBREAK
-/

inductive RV32I where
  | LUI   | AUIPC | JAL   | JALR  | BEQ   | BNE   | BLT   | BGE
  | BLTU  | BGEU  | LB    | LH    | LW    | LBU   | LHU   | SB
  | SH    | SW    | ADDI  | SLTI  | SLTIU | XORI  | ORI   | ANDI
  | SLLI  | SRLI  | SRAI  | ADD   | SUB   | SLL   | SLT   | SLTU
  | XOR   | SRL   | SRA   | OR    | AND   | FENCE | ECALL | EBREAK

instance : InstructionSet RV32I where
  all := #[
    .LUI,   .AUIPC, .JAL,   .JALR,  .BEQ,   .BNE,   .BLT,   .BGE,
    .BLTU,  .BGEU,  .LB,    .LH,    .LW,    .LBU,   .LHU,   .SB,
    .SH,    .SW,    .ADDI,  .SLTI,  .SLTIU, .XORI,  .ORI,   .ANDI,
    .SLLI,  .SRLI,  .SRAI,  .ADD,   .SUB,   .SLL,   .SLT,   .SLTU,
    .XOR,   .SRL,   .SRA,   .OR,    .AND,   .FENCE, .ECALL, .EBREAK
  ]
  encode_mnemonic (m: RV32I)
    := match m with
        | .LUI    => { type := .U,  mnemonic := U.EncMnemonic.new                       0b0110111 }
        | .AUIPC  => { type := .U,  mnemonic := U.EncMnemonic.new                       0b0010111 }
        | .JAL    => { type := .J,  mnemonic := J.EncMnemonic.new                       0b1101111 }
        | .JALR   => { type := .I,  mnemonic := I.EncMnemonic.new               0b000   0b1100111 }
        | .BEQ    => { type := .B,  mnemonic := B.EncMnemonic.new               0b000   0b1100011 }
        | .BNE    => { type := .B,  mnemonic := B.EncMnemonic.new               0b001   0b1100011 }
        | .BLT    => { type := .B,  mnemonic := B.EncMnemonic.new               0b100   0b1100011 }
        | .BGE    => { type := .B,  mnemonic := B.EncMnemonic.new               0b101   0b1100011 }
        | .BLTU   => { type := .B,  mnemonic := B.EncMnemonic.new               0b110   0b1100011 }
        | .BGEU   => { type := .B,  mnemonic := B.EncMnemonic.new               0b111   0b1100011 }
        | .LB     => { type := .I,  mnemonic := I.EncMnemonic.new               0b000   0b0000011 }
        | .LH     => { type := .I,  mnemonic := I.EncMnemonic.new               0b001   0b0000011 }
        | .LW     => { type := .I,  mnemonic := I.EncMnemonic.new               0b010   0b0000011 }
        | .LBU    => { type := .I,  mnemonic := I.EncMnemonic.new               0b100   0b0000011 }
        | .LHU    => { type := .I,  mnemonic := I.EncMnemonic.new               0b101   0b0000011 }
        | .SB     => { type := .S,  mnemonic := S.EncMnemonic.new               0b000   0b0100011 }
        | .SH     => { type := .S,  mnemonic := S.EncMnemonic.new               0b001   0b0100011 }
        | .SW     => { type := .S,  mnemonic := S.EncMnemonic.new               0b010   0b0100011 }
        | .ADDI   => { type := .I,  mnemonic := I.EncMnemonic.new               0b000   0b0010011 }
        | .SLTI   => { type := .I,  mnemonic := I.EncMnemonic.new               0b010   0b0010011 }
        | .SLTIU  => { type := .I,  mnemonic := I.EncMnemonic.new               0b011   0b0010011 }
        | .XORI   => { type := .I,  mnemonic := I.EncMnemonic.new               0b100   0b0010011 }
        | .ORI    => { type := .I,  mnemonic := I.EncMnemonic.new               0b110   0b0010011 }
        | .ANDI   => { type := .I,  mnemonic := I.EncMnemonic.new               0b111   0b0010011 }
        | .SLLI   => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b001   0b0010011 }
        | .SRLI   => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b101   0b0010011 }
        | .SRAI   => { type := .R,  mnemonic := R.EncMnemonic.new   0b0100000   0b101   0b0010011 }
        | .ADD    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b000   0b0110011 }
        | .SUB    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0100000   0b000   0b0110011 }
        | .SLL    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b001   0b0110011 }
        | .SLT    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b010   0b0110011 }
        | .SLTU   => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b011   0b0110011 }
        | .XOR    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b100   0b0110011 }
        | .SRL    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b101   0b0110011 }
        | .SRA    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0100000   0b101   0b0110011 }
        | .OR     => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b110   0b0110011 }
        | .AND    => { type := .R,  mnemonic := R.EncMnemonic.new   0b0000000   0b111   0b0110011 }
        | .FENCE  => { type := .I,  mnemonic := I.EncMnemonic.new               0b000   0b0001111 }
        | .ECALL  => { type := .Const,  mnemonic := Const.EncMnemonic.new   0b000000000000    0b00000   0b000   0b00000   0b1110011 }
        | .EBREAK => { type := .Const,  mnemonic := Const.EncMnemonic.new   0b000000000001    0b00000   0b000   0b00000   0b1110011 }
  run
    | .LUI, args
        => RegFile.set_word args.rd args.imm
    | .AUIPC, args
        => do let pc <- RegFile.get_word .PC
              RegFile.set_word .PC (pc + args.imm)
    | .JAL, args
        => do let pc <- RegFile.get_word .PC
              let newPC := pc + args.imm
              -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
              RegFile.set_word args.rd (pc + 4)
              RegFile.set_word .PC newPC
    | .JALR, args
        => do let pc <- RegFile.get_word .PC
              let newPC := pc + args.imm
              -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
              RegFile.set_word args.rd (pc + 4)
              RegFile.set_word .PC newPC
    | .BEQ, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs1
              let pc <- RegFile.get_word .PC
              if x == y then do
                let newPC := pc + args.imm
                -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
                RegFile.set_word .PC newPC
    | .BNE, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs1
              let pc <- RegFile.get_word .PC
              if x != y then do
                let newPC := pc + args.imm
                -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
                RegFile.set_word .PC newPC
    | .BLT, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs1
              let pc <- RegFile.get_word .PC
              if x < y then do  -- TODO: signed comparison!
                let newPC := pc + args.imm
                -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
                RegFile.set_word .PC newPC
    | .BGE, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs1
              let pc <- RegFile.get_word .PC
              if x >= y then do -- TODO: signed comparison!
                let newPC := pc + args.imm
                -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
                RegFile.set_word .PC newPC
    | .BLTU, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs1
              let pc <- RegFile.get_word .PC
              if x < y then do
                let newPC := pc + args.imm
                -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
                RegFile.set_word .PC newPC
    | .BGEU, args
        => do let x <- RegFile.get_word args.rs1
              let y <- RegFile.get_word args.rs1
              let pc <- RegFile.get_word .PC
              if x >= y then do
                let newPC := pc + args.imm
                -- TODO: instruction-address-misaligned exception if newPC % 4 != 0
                RegFile.set_word .PC newPC
    | .LB, args
        => do pure ()
    | .LH, args
        => do pure ()
    | .LW, args
        => do pure ()
    | .LBU, args
        => do pure ()
    | .LHU, args
        => do pure ()
    | .SB, args
        => do pure ()
    | .SH, args
        => do pure ()
    | .SW, args
        => do pure ()
    | .ADDI, args
        => do pure ()
    | .SLTI, args
        => do pure ()
    | .SLTIU, args
        => do pure ()
    | .XORI, args
        => do pure ()
    | .ORI, args
        => do pure ()
    | .ANDI, args
        => do pure ()
    | .SLLI, args
        => do pure ()
    | .SRLI, args
        => do pure ()
    | .SRAI, args
        => do pure ()
    | .ADD, args
        => do pure ()
    | .SUB, args
        => do pure ()
    | .SLL, args
        => do pure ()
    | .SLT, args
        => do pure ()
    | .SLTU, args
        => do pure ()
    | .XOR, args
        => do pure ()
    | .SRL, args
        => do pure ()
    | .SRA, args
        => do pure ()
    | .OR, args
        => do pure ()
    | .AND, args
        => do pure ()
    | .FENCE, args
        => do pure ()
    | .ECALL, args
        => do pure ()
    | .EBREAK, args
        => do pure ()

end RiscV.Instr.InstrRV32I
