A0,A1,A2,A3,A4,A5,A6,A7,A8,B0,B1,B2,B3,B4,B5,B6,B7,B8,C0,C1,C2,C3,C4,C5,C6,C7,C8,E0,E1,E2,E3,E4,E5,E6,E7,E8
PA,PB,PC,Chan3,Chan2,Chan1,Chan0

NOT NA0 A0
NOT NA1 A1
NOT NA2 A2
NOT NA3 A3
NOT NA4 A4
NOT NA5 A5
NOT NA6 A6
NOT NA7 A7
NOT NA8 A8

AND NPA NA0 NA1 NA2 NA3 NA4 NA5 NA6 NA7 NA8
NOT PA NPA

XOR X10 NA0 E0
XOR X11 NA1 E1
XOR X12 NA2 E2
XOR X13 NA3 E3
XOR X14 NA4 E4
XOR X15 NA5 E5
XOR X16 NA6 E6
XOR X17 NA7 E7
XOR X18 NA8 E8

NOT NE0 E0
NOT NE1 E1
NOT NE2 E2
NOT NE3 E3
NOT NE4 E4
NOT NE5 E5
NOT NE6 E6
NOT NE7 E7
NOT NE8 E8

NOR NEB0 NE0 B0
NOR NEB1 NE1 B1
NOR NEB2 NE2 B2
NOR NEB3 NE3 B3
NOR NEB4 NE4 B4
NOR NEB5 NE5 B5
NOR NEB6 NE6 B6
NOR NEB7 NE7 B7
NOR NEB8 NE8 B8

AND NEBX0 NEB0 X10
AND NEBX1 NEB1 X11
AND NEBX2 NEB2 X12
AND NEBX3 NEB3 X13
AND NEBX4 NEB4 X14
AND NEBX5 NEB5 X15
AND NEBX6 NEB6 X16
AND NEBX7 NEB7 X17
AND NEBX8 NEB8 X18

NOT NNEBX0 NEBX0
NOT NNEBX1 NEBX1
NOT NNEBX2 NEBX2
NOT NNEBX3 NEBX3
NOT NNEBX4 NEBX4
NOT NNEBX5 NEBX5
NOT NNEBX6 NEBX6
NOT NNEBX7 NEBX7
NOT NNEBX8 NEBX8

AND NPB NNEBX0 NNEBX1 NNEBX2 NNEBX3 NNEBX4 NNEBX5 NNEBX6 NNEBX7 NNEBX8
NOT PB NPB

XOR X20 NNEBX0 PB
XOR X21 NNEBX1 PB
XOR X22 NNEBX2 PB
XOR X23 NNEBX3 PB
XOR X24 NNEBX4 PB
XOR X25 NNEBX5 PB
XOR X26 NNEBX6 PB
XOR X27 NNEBX7 PB
XOR X28 NNEBX8 PB

NOR NEC0 NE0 C0
NOR NEC1 NE1 C1
NOR NEC2 NE2 C2
NOR NEC3 NE3 C3
NOR NEC4 NE4 C4
NOR NEC5 NE5 C5
NOR NEC6 NE6 C6
NOR NEC7 NE7 C7
NOR NEC8 NE8 C8

AND RC0 NEC0 X10 X20
AND RC1 NEC1 X11 X21
AND RC2 NEC2 X12 X22
AND RC3 NEC3 X13 X23
AND RC4 NEC4 X14 X24
AND RC5 NEC5 X15 X25
AND RC6 NEC6 X16 X26
AND RC7 NEC7 X17 X27
AND RC8 NEC8 X18 X28

NOT NRC0 RC0
NOT NRC1 RC1
NOT NRC2 RC2
NOT NRC3 RC3
NOT NRC4 RC4
NOT NRC5 RC5
NOT NRC6 RC6
NOT NRC7 RC7
NOT NRC8 RC8

AND NPC NRC0 NRC1 NRC2 NRC3 NRC4 NRC5 NRC6 NRC7 NRC8
NOT PC NPC

NAND APA0 A0 PA
NAND APA1 A1 PA
NAND APA2 A2 PA
NAND APA3 A3 PA
NAND APA4 A4 PA
NAND APA5 A5 PA
NAND APA6 A6 PA
NAND APA7 A7 PA
NAND APA8 A8 PA

NAND BPB0 B0 PB
NAND BPB1 B1 PB
NAND BPB2 B2 PB
NAND BPB3 B3 PB
NAND BPB4 B4 PB
NAND BPB5 B5 PB
NAND BPB6 B6 PB
NAND BPB7 B7 PB
NAND BPB8 B8 PB

NAND CPC0 C0 PC
NAND CPC1 C1 PC
NAND CPC2 C2 PC
NAND CPC3 C3 PC
NAND CPC4 C4 PC
NAND CPC5 C5 PC
NAND CPC6 C6 PC
NAND CPC7 C7 PC
NAND CPC8 C8 PC

AND NNI0 APA0 BPB0 CPC0 E0
AND NNI1 APA1 BPB1 CPC1 E1
AND NNI2 APA2 BPB2 CPC2 E2
AND NNI3 APA3 BPB3 CPC3 E3
AND NNI4 APA4 BPB4 CPC4 E4
AND NNI5 APA5 BPB5 CPC5 E5
AND NNI6 APA6 BPB6 CPC6 E6
AND NNI7 APA7 BPB7 CPC7 E7
AND NNI8 APA8 BPB8 CPC8 E8

NOT I0 NNI0
NOT I1 NNI1
NOT I2 NNI2
NOT I3 NNI3
NOT I4 NNI4
NOT I5 NNI5
NOT I6 NNI6
NOT I7 NNI7
NOT I8 NNI8

NOT NI8 I8
AND AI07 I0 I1 I2 I3 I4 I5 I6 I7
NOR Chan3 AI07 NI8

NOT NI5 I5
NAND NNI56 I6 NI5
AND NChan2 I7 I6 I4 NNI56
NOT Chan2 NChan2

NOT NI2 I2
AND NNNI245 I5 I4 NI2
NOT NNI245 NNNI245
AND NNI6543 I6 I5 I4 I3
NOT NI6543 NNI6543
AND NChan1 I7 I6 NNI245 NI6543
NOT Chan1 NChan1

NOT NI1 I1
AND NNI1256 NI1 I2 I5 I6
NOT NI1256 NNI1256
AND NChan0 I7 NNI56 NI6543 NI1256
NOT Chan0 NChan0