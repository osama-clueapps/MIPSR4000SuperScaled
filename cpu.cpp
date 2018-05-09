#include<iostream>
#include<string>
#include "gui.h"
#include"instCU.h"
#include"buffer_1.h"
#include"buffer_2.h"
#include"buffer_3.h"
#include"buffer_4.h"
#include"buffer_5.h"
#include"buffer_6.h"
#include"buffer_7.h"
#include "nextpc.h"
#include"dmem.h"
#include"imem.h"
#include"RegFile.h"
#include "HazardUnit.h"
#include <fstream>
#include"assembly.h"
#include "code.h"
#include <stack>
#include "BTB.h"
#include"complete.h"
#include"Dispatch.h"
#include"HazardUnitS.h"
using namespace std;
nextpc nx;
int arr[50][2];
unsigned int nextPC;
int branchsignal = 0;
stack <unsigned int> stck;
GUI g;
vector <int> com;
int previousstall1 = 0, previousstall2 = 0;
bool usejal1 = 0, usejal2 = 0;
bool usenextinst1 = false, usenextinst2 = false;
int branch1instnum = 0;
int branch2instnum = 0;
int nextinst = 0;
bool usereturn1 = 0, usereturn2 = 0;
int return1num = 0, return2num = 0;
bool usejr1 = 0, usejr2 = 0;
void datapath(assembly &f);

void ALU(int a, int b, int ALU_CT, int &result, int &z);
void PC(unsigned int pcin, unsigned int &pcout, bool en);
void print1();
void print2();
void print3();
void print4();
void print5();
void print5_1();
void print6();
void print7();
void IF();
void EXStage();
void RFStage();
void muxforALUs();
void FlushUnit();
void intersectingStalls();
void handlePC();
unsigned int inst1 = 0, inst2 = 0;
int clk = 0, rst;
int both = 0;
int stackpc = 0;
int jr1instnum = 0, jr2instnum = 0;
bool jump1 = 0, jump2 = 0;
//buffers
buffer_1 buf1;
buffer_2 buf2a, buf2b;
buffer_3 buf3;
buffer_4 buf4;
buffer_5 buf5;
buffer_6 buf6;
buffer_7 buf7;
//instdec and CU
instCU cu;
//PC
unsigned int pcin = 0, pcout = -4;
unsigned int pcofbranch = -1;
//IM
imem im;
//RegFile
RegFile rf;
unsigned int comp = 0, PCSrcD = 0;
int PCBranchD = 0, PCJump;
int c1 = 0, c2 = 0, rd1 = 0, rd2 = 0;
//ALU
int SrcAE = 0, SrcBE = 0, aluoutE, z, WriteDataE, WriteRegE;
//BTB
BTB b;
//Dmem
dmem dm;
int ResultW = 0;
unsigned int ReadDataM2 = 0;
int Pbfailedt1 = 0, Pbfailednt1 = 0;
int Pbfailedt2 = 0, Pbfailednt2 = 0;
bool  usejumpinst2 = false;
bool  usejumpinst1 = false;
int jump1instnum = 0;
int jump2instnum = 0;
bool jumpr1 = false, jumpr2 = false;
int cnt = 0;
vector <Code> code;
ofstream target;
assembly a;
HazardUnit h;
Dispatch d;
HazardUnitS hs;
int jal1instnum = 0, jal2instnum = 0;
int stall1 = 0, stall2 = 0;

instCU cu1, cu2;
buffer_3 buf3a, buf3b;
int rd1a, rd2a, rd1b, rd2b;
HazardUnit h1, h2;
int c1a, c1b, c2a, c2b;
unsigned int inst1D, inst2D;
complete c;
int pcout1 = -8, pcin1 = -8, pcout2 = -4, pcin2 = -4;
buffer_1 buf1a, buf1b;
buffer_7 buf7a, buf7b, buf7c;
int comp1, comp2;
int PCSrcDA, PCSrcDB, PCBranchDA, PCBranchDB;
int pcofbranch1, pcofbranch2, PCJumpA, PCJumpB;
int SrcAE1, SrcBE1, SrcAE2, SrcBE2;
int WriteDataE1, WriteDataE2, WriteRegE1, WriteRegE2, aluoutE1, aluoutE2;

void dp()
{
	if (clk > 1)
	{
		d.inputData(buf2a.instD, buf2a.inst_num, buf2b.instD, buf2b.inst_num);
		d.outputData(2);
		if (cu1.jump || cu2.jump || cu1.pushstack==2 || cu2.pushstack==2) {
			d.inst1 = 0;
			d.inst2 = 0;
		}
	}

	cu1.setinst(d.inst1);

	cu2.setinst(d.inst2);
	WriteRegE1 = (buf3a.RegDstE == 0) ? buf3a.RtE : buf3a.RdE;
	WriteRegE2 = (buf3b.RegDstE == 0) ? buf3b.RtE : buf3b.RdE;
	h1.inputData(cu1.RsD, buf3a.RsE, cu1.RtD, buf3a.RtE, buf3a.MemtoRegE, cu1.branch,
		buf3a.RegWriteE, buf3a.MemtoRegE, buf4.MemtoRegM, buf4.WriteRegM,
		PCSrcDA, buf5.WriteRegM2, buf6.WriteRegM3, buf4.RegWriteM,
		buf5.RegWriteM2, buf6.RegWriteM3, buf3a.RegDstE, buf3a.RdE,
		buf7.WriteRegW, buf7.RegWriteW, WriteRegE1);
	h2.inputData(cu2.RsD, buf3.RsE, cu2.RtD, buf3b.RtE, buf3b.MemtoRegE, cu2.branch,
		buf3b.RegWriteE, buf3b.MemtoRegE, buf4.MemtoRegM, buf4.WriteRegM,
		PCSrcDB, buf5.WriteRegM2, buf6.WriteRegM3, buf4.RegWriteM,
		buf5.RegWriteM2, buf6.RegWriteM3, buf3b.RegDstE, buf3b.RdE,
		buf7.WriteRegW, buf7.RegWriteW, WriteRegE2);
	h1.updateData();
	h2.updateData();

	//IF
	IF();
	//IF2
	Code cc;
	//forGUI
	if (clk > 0) {
		if (inst1 != 0xffffffff && pcout1 / 4 < a.inst.size() - 1 && a.inst[pcout1 / 4] != 0x0) {
			if (a.inst[pcout1 / 4] != 0)
				cc.setDetails(a.instructions[pcout1 / 4], a.inst[pcout1 / 4], pcout1);
			else
				cc.setDetails("", 0, 0);
		}
		else
			cc.setDetails("End", 0, 0);
		code.push_back(cc);
		if (inst2 != 0xffffffff && pcout2 / 4 < a.inst.size() - 1 && a.inst[pcout2 / 4] != 0x0) {
			if (a.inst[pcout2 / 4] != 0)
				cc.setDetails(a.instructions[pcout2 / 4], a.inst[pcout2 / 4], pcout2);
			else
				cc.setDetails("", 0, 0);
		}
		else
			cc.setDetails("End", 0, 0);
		code.push_back(cc);
	}

	im.IF2(buf1a.PC_out, inst1);
	im.IF2(buf1b.PC_out, inst2);
	if (!h1.StallD && !stall1) {
		buf2a.inputData(inst1, pcout1 + 4);
		if (buf1a.inst_num >= 0 && buf1a.PC_out/4<a.instructions.size()) {

			g.code[buf1a.inst_num][0].setString(to_string(buf1a.PC_out));
			g.code[buf1a.inst_num][1].setString(a.instructions[buf1a.PC_out/4]);
		}
	}
	if (!h2.StallD && !stall2) {
		buf2b.inputData(inst2, pcout2 + 4);
		if (buf1b.inst_num >= 0 && buf1b.PC_out / 4<a.instructions.size()) {
			g.code[buf1b.inst_num][0].setString(to_string(buf1b.PC_out));
			g.code[buf1b.inst_num][1].setString(a.instructions[buf1b.PC_out/4]);
		}
	}
	
	if (clk > 1)
	{
		if (!h1.StallD) {
			buf2a.setInstNum(buf1a.inst_num, buf1a.pc);
			if(buf1a.inst_num>=0)
			g.stages[buf1a.inst_num][clk - 1].setString("IS");
		}
		else 
			g.stages[buf1a.inst_num][clk - 1].setString("IS");
		
		/*else {

			g.stages[buf1a.inst_num][clk - 1].setString("IS");
		}*/

		if (!h2.StallD) {
			buf2b.setInstNum(buf1b.inst_num, buf1b.pc);
			g.stages[buf1b.inst_num][clk - 1].setString("IS");
		}
		else
			g.stages[buf1b.inst_num][clk - 1].setString("IS");
		/*else {
			g.stages[buf1b.inst_num][clk - 1].setString("IS");
		}*/
	}

	//Dispatch

	//
	c.insert(buf7a.inst_num, buf7a.ReadDataW, buf7a.RegWriteW, buf7a.MemtoRegW, buf7a.ALUOutW, buf7a.WriteRegW,arr);
	if(buf7a.inst_num>=0 && g.stages[buf7a.inst_num][clk - 2].getString()!="C/WB"&& g.stages[buf7a.inst_num][clk - 2].getString() != " ")
	g.stages[buf7a.inst_num][clk - 1].setString("C");
	
	c.insert(buf7b.inst_num, buf7b.ReadDataW, buf7b.RegWriteW, buf7b.MemtoRegW, buf7b.ALUOutW, buf7b.WriteRegW,arr);
	if (buf7b.inst_num >= 0)
	g.stages[buf7b.inst_num][clk - 1].setString("C");
	
	c.insert(buf7c.inst_num, buf7c.ReadDataW, buf7c.RegWriteW, buf7c.MemtoRegW, buf7c.ALUOutW, buf7c.WriteRegW,arr);
	if (buf7c.inst_num >= 0)
	g.stages[buf7c.inst_num][clk - 1].setString("C");
	
	
	cout << "%%%%%%%%%		" << clk << endl;
	c.print();	
	EXStage();

	while (c.getnext())
	{
		unsigned int WriteReg, ReadData, MemtoReg, RegWrite, Aluout;

		int k= c.next(ReadData, RegWrite, MemtoReg, Aluout, WriteReg,arr);
		if(k>=0)
		g.stages[k][clk - 1].setString("C/WB");

		ResultW = (MemtoReg == 1) ? ReadData : Aluout;
		if (RegWrite) {
			rf.writeRegFile(WriteReg, ResultW);

		}
	}
	RFStage();
	print2();


	print5();
	buf5.inputData(buf4.RegWriteM, buf4.MemtoRegM, buf4.MemWriteM, buf4.ALUOutM, buf4.WriteDataM, buf4.WriteRegM);
	target << "--------------------------------------------------" << endl << endl;
	//DF
	dm.DF1();
	print5_1();
	if (clk > 5) {
		buf5.setInstNum(buf4.inst_num, buf4.pc);
		if (buf4.inst_num >= 0)
		g.stages[buf4.inst_num][clk - 1].setString("DF");
	}
	target << "--------------------------------------------------" << endl << endl;
	//DS
	dm.DF2(buf5.ALUOutM2, buf5.MemWriteM2, buf5.WriteDataM2, ReadDataM2);
	buf6.inputData(buf5.RegWriteM2, ReadDataM2, buf5.MemtoRegM2, buf5.ALUOutM2, buf5.WriteRegM2);
	print6();
	if (clk > 6) {
		buf6.setInstNum(buf5.inst_num, buf5.pc);
		if (buf5.inst_num >= 0)
		g.stages[buf5.inst_num][clk - 1].setString("DS");
	}
	target << "--------------------------------------------------" << endl << endl;
	//TC
	dm.TC();
	buf7c.inputData(buf6.RegWriteM3, buf6.ReadDataM3, buf6.MemtoRegM3, buf6.ALUOutM3, buf6.WriteRegM3);
	print7();
	if (clk > 7) {

		buf7c.setInstNum(buf6.inst_num, buf6.pc);
		if (buf6.inst_num >= 0)
		g.stages[buf6.inst_num][clk - 1].setString("TC");
	}
	target << "--------------------------------------------------" << endl << endl;
	//Buffers update

	buf1a.updateData();
	buf1b.updateData();

	buf3a.updateData();
	buf3b.updateData();

	buf2a.updateData();
	buf2b.updateData();
	
	FlushUnit();
	
	buf4.updateData();
	buf5.updateData();
	buf6.updateData();
	buf7a.updateData();
	buf7b.updateData();
	buf7c.updateData();
}



int main() {
	assembly file;
	string s;
	for (int i = 0; i < 50; i++) {
		arr[i][0] = i;
		arr[i][1] = i;
	}
	cout << "Enter Filename: ";
	cin >> s;
	if (file.readFile(s)) {
		cout << "processing... " << endl;
		g.readASM(file.instructions);
		datapath(file);
	}
	else
		cout << "error file" << endl;
	system("Pause");
	return 0;
}
void ALU(int a, int b, int ALU_CT, int &result, int &z) {

	switch (ALU_CT) {
	case 0:
		result = a & b;
		break;
	case 1:
		result = a - b;
		break;
	case 2:
		result = a + b;
		break;
	case 4:
		result = a ^ b;
		break;
	case 6:
		result = a - b;
		break;
	case 7:
		result = a < b;
	default:
		result = result;
	}
	if (result == 0) z = 1;
}

void PC(int pcin, int& pcout, bool en)
{
	if (en)
		pcout = pcin;
}

void datapath(assembly &f)
{
	a = f;
	unsigned int inst = 0;
	for (int i = 0; i < f.inst.size(); i++)
	{
		im.WriteInst(i * 4, f.inst[i]);
		cout << f.inst[i] << endl;
	}
	target.open("target.txt");
	//b.fillVector(f.inst);
	buf1b.PC_out = -4;
	buf1a.PC_out = -4;

	while (clk<47 && g.window.isOpen())
	{
		g.handleEvents();
		if (g.keypressed) {

			clk++;
			dp();
			g.updateRegFile(rf);
			g.updateDmem(dm);
			g.updateBTB(b);
		
			g.updateStack(stck);
		
			
		}
		g.display(code);
	}
	for (int i = 0; i < 16; i++)
	{
		cout << dec << i << "\t" << dec << rf.file[i] << endl;
	}
}
void print1()
{
	target << "\t\t\t\t\t\t\t Cycle " << clk << endl;
	target << "IF stage: " << endl;
	target << "PCSrcD: " << PCSrcD << endl;
	target << "PC1: " << pcout1 << endl;
	target << "PC2: " << pcout2 << endl;
	//target << "PCBRANCHD !!!!!!!!  " << dec << PCBranchD << endl;
	target << "StallF: " << h.StallF << endl;
	target << "--------------------------------------------------" << endl << endl;
}
void print2()
{
	target << "WB stage: " << endl;
	target << "MemtoRegW: " << buf7.MemtoRegW << endl;
	target << "ALUOutW: " << buf7.ALUOutW << endl;
	target << "ReadDataW: " << buf7.ReadDataW << endl;
	target << "RegWriteW: " << buf7.RegWriteW << endl;
	target << "WriteRegW: " << buf7.WriteRegW << endl;
	target << "ResultW: " << ResultW << endl;
	target << "====================================================================" << endl << endl;
}
void print3()
{
	target << "IS stage: " << endl;
	target << "Instruction1: " << hex << inst1 << endl;
	target << "Instruction2: " << hex << inst2 << endl;
	target << "StallD: " << h.StallD << endl;
	target << "PCSrcA: " << dec << PCSrcDA << endl;
	target << "PCSrcB: " << dec << PCSrcDB << endl;
	target << "--------------------------------------------------" << endl << endl;
}
void print4()
{
	target << "RF stage: " << endl;
	target << "				CONTROL UNIT 1	" << endl;
	target << "ForwardAD " << h1.ForwardAD << endl;
	target << "ForwardBD " << h1.ForwardBD << endl;
	target << "FlushE: " << h1.FlushE << endl;
	target << "InstructionD: " << hex << buf2a.instD << endl;

	target << "BRANCHING" << endl;
	target << "cu1.branch: " << cu1.branch << endl;
	target << "c1: " << c1a << endl;
	target << "c2: " << c1b << endl;
	target << "comp1: " << comp1 << endl;
	target << "pbfailednt1: " << Pbfailednt1 << endl;
	target << "pbfailedt1: " << Pbfailedt1 << endl;
	target << "PCSRCDA: " << PCSrcDA << endl;

	target << "A1: " << cu1.A1 << endl;
	target << "A2: " << cu1.A2 << endl;
	target << "RD1: " << rd1a << endl;
	target << "RD2: " << rd2a << endl;
	target << "RegWriteD: " << cu1.RegWrite << endl;
	target << "MemtoRegD: " << cu1.MemtoReg << endl;
	target << "MemWriteD: " << cu1.MemWrite << endl;
	target << "ALUControlD: " << cu1.aluctrl << endl;
	target << "ALUSrc: " << cu1.alusrc << endl;
	target << "RegDstD: " << cu1.RegDst << endl;
	target << "JumpD: " << cu1.jump << endl;
	target << "BranchD: " << cu1.branch << endl;
	target << "RsD: " << cu1.RsD << endl;
	target << "RtD: " << cu1.RtD << endl;
	target << "RdE: " << cu1.RdE << endl;
	target << "I-imm: " << cu1.Iimm << endl;
	target << "J-imm: " << cu1.Jimm << endl;

	target << "				CONTROL UNIT 2	" << endl;
	target << "ForwardAD " << h2.ForwardAD << endl;
	target << "ForwardBD " << h2.ForwardBD << endl;
	target << "FlushE: " << h2.FlushE << endl;
	target << "InstructionD: " << hex << buf2b.instD << endl;

	target << "BRANCHING" << endl;
	target << "cu2.branch: " << cu2.branch << endl;
	target << "c1: " << c2a << endl;
	target << "c2: " << c2b << endl;
	target << "comp2: " << comp2 << endl;
	target << "pbfailednt2: " << Pbfailednt2 << endl;
	target << "pbfailedt2: " << Pbfailedt2 << endl;
	target << "PCSRCDB: " << PCSrcDB << endl;
	target << "A1: " << cu2.A1 << endl;
	target << "A2: " << cu2.A2 << endl;
	target << "RD1: " << rd1b << endl;
	target << "RD2: " << rd2b << endl;
	target << "RegWriteD: " << cu2.RegWrite << endl;
	target << "MemtoRegD: " << cu2.MemtoReg << endl;
	target << "MemWriteD: " << cu2.MemWrite << endl;
	target << "ALUControlD: " << cu2.aluctrl << endl;
	target << "ALUSrc: " << cu2.alusrc << endl;
	target << "RegDstD: " << cu2.RegDst << endl;
	target << "JumpD: " << cu2.jump << endl;
	target << "BranchD: " << cu2.branch << endl;
	target << "RsD: " << cu2.RsD << endl;
	target << "RtD: " << cu2.RtD << endl;
	target << "RdE: " << cu2.RdE << endl;
	target << "I-imm: " << cu2.Iimm << endl;
	target << "J-imm: " << cu2.Jimm << endl;
}
void print5()
{
	target << "EX stage: " << endl;

	target << "										EX UNIT 1" << endl;
	target << "RegDstE: " << buf3a.RegDstE << endl;
	target << "ALUSrcE: " << buf3a.ALUSrcE << endl;
	target << "ALUControlE: " << buf3a.ALUControlE << endl;
	target << "SrcAE: " << SrcAE1 << endl;
	target << "SrcBE: " << SrcBE1 << endl;
	target << "ALUResult: " << aluoutE1 << endl;
	target << "RegWriteE: " << buf3a.RegWriteE << endl;
	target << "MemtoRegE: " << buf3a.MemtoRegE << endl;
	target << "MemWriteE: " << buf3a.MemWriteE << endl;
	target << "WriteDataE: " << WriteDataE1 << endl;
	target << "WriteRegE: " << WriteRegE1 << endl;
	target << "buf3.RsE: " << buf3a.RsE << endl;
	target << "Buf4.WriteregM: " << buf4.WriteRegM << endl;
	target << "Buf5.WriteRegM2: " << buf5.WriteRegM2 << endl;
	target << "Buf6.WriteRegM3: " << buf6.WriteRegM3 << endl;
	target << "Buf7.WriteRegW: " << buf7.WriteRegW << endl;
	target << "FA: " << h1.ForwardAE << endl;
	target << "FB: " << h1.ForwardBE << endl;

	target << "										EX UNIT 1" << endl;
	target << "RegDstE: " << buf3b.RegDstE << endl;
	target << "ALUSrcE: " << buf3b.ALUSrcE << endl;
	target << "ALUControlE: " << buf3b.ALUControlE << endl;
	target << "SrcAE: " << SrcAE2 << endl;
	target << "SrcBE: " << SrcBE2 << endl;
	target << "ALUResult: " << aluoutE2 << endl;
	target << "RegWriteE: " << buf3b.RegWriteE << endl;
	target << "MemtoRegE: " << buf3b.MemtoRegE << endl;
	target << "MemWriteE: " << buf3b.MemWriteE << endl;
	target << "WriteDataE: " << WriteDataE2 << endl;
	target << "WriteRegE: " << WriteRegE2 << endl;
	target << "buf3.RsE: " << buf3b.RsE << endl;
	target << "Buf4.WriteregM: " << buf4.WriteRegM << endl;
	target << "Buf5.WriteRegM2: " << buf5.WriteRegM2 << endl;
	target << "Buf6.WriteRegM3: " << buf6.WriteRegM3 << endl;
	target << "Buf7.WriteRegW: " << buf7.WriteRegW << endl;
	target << "FA: " << h2.ForwardAE << endl;
	target << "FB: " << h2.ForwardBE << endl;
}
void print5_1()
{
	target << "DF stage: " << endl;
	target << "RegWriteM: " << buf4.RegWriteM << endl;
	target << "MemtoRegM: " << buf4.MemtoRegM << endl;
	target << "MemWriteM: " << buf4.MemWriteM << endl;
	target << "ALUOutM: " << buf4.ALUOutM << endl;
	target << "WriteDataM: " << buf4.WriteDataM << endl;
	target << "WriteRegM: " << buf4.WriteRegM << endl;
}
void print6()
{
	target << "DS stage: " << endl;
	target << "RegWriteM2: " << buf5.RegWriteM2 << endl;
	target << "MemtoRegM2: " << buf5.MemtoRegM2 << endl;
	target << "MemWriteM2: " << buf5.MemWriteM2 << endl;
	target << "ALUOutM2: " << buf5.ALUOutM2 << endl;
	target << "WriteDataM2: " << buf5.WriteDataM2 << endl;
	target << "WriteRegM2: " << buf5.WriteRegM2 << endl;
	target << "ReadDataM2: " << ReadDataM2 << endl;
}
void print7()
{
	target << "TC stage: " << endl;
	target << "RegWriteM3: " << buf6.RegWriteM3 << endl;
	target << "MemtoRegM3: " << buf6.MemtoRegM3 << endl;
	target << "ALUOutM3: " << buf6.ALUOutM2 << endl;
	target << "WriteRegM3: " << buf6.WriteRegM3 << endl;
	target << "ReadDataM3: " << buf6.ReadDataM3 << endl;
}
void IF()
{
	handlePC();

	PC(pcin1, pcout1, !h1.StallF && !stall1 && !h2.StallF && !stall2);
	PC(pcin2, pcout2, !h1.StallF && !stall1 && !h2.StallF && !stall2);
	im.IF1();

	if (b.isBranch(buf1a.pc)!=-1) {
		int n=nx.predictBranch(b, buf1a.pc);
		if (n != -1) {
			pcout1 = n;
			pcout2 = n + 4;
		}

	}

	if (clk == 1)
		pcout1 = 0;
	
		buf1a.setInstNum(cnt, pcout1);
		g.stages[cnt][clk - 1].setString("IF");
		cnt++;
		
		buf1b.setInstNum(cnt, pcout2);
		g.stages[cnt][clk - 1].setString("IF");
		cnt++;
	

	buf1a.inputData(pcout1);
	buf1b.inputData(pcout2);
	print1();
}
void RFStage()
{
	rf.readRegFile(cu1.A1, cu1.A2, rd1a, rd2a);
	rf.readRegFile(cu2.A1, cu2.A2, rd1b, rd2b);
	if (clk > 2)
	{
		buf3a.setInstNum(d.instNum1, buf2a.pc);
		if (d.instNum1 >= 0)
			g.stages[d.instNum1][clk - 1].setString("DISP/RF");


		buf3b.setInstNum(d.instNum2, buf2b.pc);
		if (d.instNum2 >= 0)
			g.stages[d.instNum2][clk - 1].setString("DISP/RF");


	if (g.stages[d.instNum1 + 1][clk - 2].getString() == "IS")
			g.stages[d.instNum1 + 1][clk - 1].setString("DISP/RF");

		if (g.stages[buf2b.inst_num - 1][clk - 1].getString() == "DISP/RF" &&  g.stages[buf2b.inst_num - 2][clk - 1].getString() == "DISP/RF" && g.stages[buf2b.inst_num][clk - 2].getString() == "IS")
		g.stages[buf2b.inst_num][clk - 1].setString("IS");

		/*	if(previousstall1)
				g.stages[d.instNum1 -1][clk - 1].setString("DISP/RF");*/
	}


	buf3a.inputData(cu1.RegWrite, cu1.MemtoReg, cu1.MemWrite, cu1.aluctrl, cu1.alusrc, cu1.RegDst, rd1a, rd2a, cu1.RsD, cu1.RtD, cu1.RdE, cu1.Iimm);
	buf3b.inputData(cu2.RegWrite, cu2.MemtoReg, cu2.MemWrite, cu2.aluctrl, cu2.alusrc, cu2.RegDst, rd1b, rd2b, cu2.RsD, cu2.RtD, cu2.RdE, cu2.Iimm);

	switch (h1.ForwardBD)
	{
	case 0: c1b = c.isComp(cu1.A2) ? c.find(cu1.A2) : rd2a;
		break;
	case 2: c1b = buf4.ALUOutM;
		break;
	case 3: c1b = buf5.ALUOutM2;
		break;
	case 4: c1b = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	switch (h1.ForwardAD)
	{

	case 0: c1a = c.isComp(cu1.A1) ? c.find(cu1.A1) : rd1a;
		break;
	case 1:c1a = aluoutE1;
		break;
	case 2: c1a = buf4.ALUOutM;
		break;
	case 3: c1a = buf5.ALUOutM2;
		break;
	case 4: c1a = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	switch (h2.ForwardBD)
	{
	case 0: c2b = c.isComp(cu2.A2) ? c.find(cu2.A2) : rd2b;
		break;
	case 2: c2b = buf4.ALUOutM;
		break;
	case 3: c2b = buf5.ALUOutM2;
		break;
	case 4: c2b = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	switch (h2.ForwardAD)
	{
	case 0: c2a = c.isComp(cu2.A1) ? c.find(cu2.A1) : rd1b;
		break;
	case 2: c2a = buf4.ALUOutM;
		break;
	case 3: c2a = buf5.ALUOutM2;
		break;
	case 4: c2a = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	comp1 = (c1a <= c1b) ? 1 : 0;
	comp2 = (c2a <= c2b) ? 1 : 0;
	PCSrcDA = (cu1.jump || (cu1.branch && comp1));
	PCSrcDB = (cu2.jump || (cu2.branch && comp2));

	PCBranchDA = cu1.Iimm * 4 + 4 + buf2a.pc;
	PCBranchDB = cu2.Iimm * 4 + 4+ buf2b.pc;
	
	if (b.isBranch(buf2b.pc)!=-1) {
		int state = nx.fixbranch(b, PCSrcDB, buf2b.pc);
		if (state != -1) {
			if (state == 3) {
				//branch should not be taken
				//pcin1=buf2b.pc
				//pcin2=pcin1+4
				branchsignal = 1;
				nextPC = buf2b.pc+4;
				h2.updatePCSrc(1);
			}
			else {
				//pcin1=state;
				//pcin2=pcin1+4;
				branchsignal = 2;
				nextPC = state;
				h2.updatePCSrc(1);
			}
		}
		else {
			//dont do anything
			branchsignal = 3;
			h2.updatePCSrc(0);
		}

	}
	
	if (b.isBranch(buf2a.pc)!=-1) {
		int state=nx.fixbranch(b, PCSrcDA, buf2a.pc);
		if (state != -1) {
			if (state == 3) {
				//branch should not be taken
				//pcin1=buf2b.pc
				//pcin2=pcin1+4
				branchsignal = 1;
				nextPC = buf2a.pc+4;
				h1.updatePCSrc(1);
			}
			else {
				//pcin1=state;
				//pcin2=pcin1+4;
				branchsignal = 2;
				nextPC = state;
				h1.updatePCSrc(1);
			}
		}
		else {
			//dont do anything
			branchsignal = 3;
			h1.updatePCSrc(0);
		}

	}


	if (cu1.branch && !previousstall1) {
		if(b.isBranch(buf2a.pc)==-1)
		b.addBranch(buf2a.pc , comp1,PCBranchDA);
		
	}
	if (cu2.branch && !previousstall2) {
		if (b.isBranch(buf2b.pc) == -1)
		b.addBranch(buf2b.pc , comp2,PCBranchDB);
	}

	


	previousstall1 = h1.StallD;
	previousstall2 = h2.StallD;
	PCJumpA = ((pcout1 >> 28) << 28) | (cu1.Jimm * 4);
	PCJumpB = ((pcout2 >> 28) << 28) | (cu2.Jimm * 4);

	nx.setInput(cu1.jump, cu2.jump, cu1.branch, cu2.branch, cu1.jumpr, cu2.jumpr,
		cu1.pushstack == 2, cu2.pushstack == 2, cu1.pushstack == 1, cu2.pushstack == 1,
		pcout1, pcout2, cu1.Jimm, cu2.Jimm, PCBranchDA, PCBranchDB,c1a,c2a);

	if (cu1.jump || cu1.jumpr || cu1.pushstack == 2||(cu1.branch&&PCSrcDA))
		h1.updatePCSrc(1);

	else h1.updatePCSrc(0);
	if (cu2.jump || cu2.jumpr|| cu2.pushstack == 2||(cu2.branch&&PCSrcDB))
		h2.updatePCSrc(1);
	else h2.updatePCSrc(0);
	if (cu1.pushstack == 1)
		stck.push(buf2a.pc+4);

	if (cu2.pushstack == 1) {
		stck.push(buf2b.pc + 4);
	}

	print4();
}


void EXStage() {

	muxforALUs();
	ALU(SrcAE1, SrcBE1, buf3a.ALUControlE, aluoutE1, z);
	ALU(SrcAE2, SrcBE2, buf3b.ALUControlE, aluoutE2, z);

	if (buf3a.MemtoRegE || buf3a.MemWriteE)
	{
		buf7a.clr();
		buf4.inputData(buf3a.RegWriteE, buf3a.MemtoRegE, buf3a.MemWriteE, aluoutE1, WriteDataE1, WriteRegE1);
		if (clk > 3) {
			buf4.setInstNum(buf3a.inst_num, buf3a.pc);
			if (buf3a.inst_num >= 0)
			g.stages[buf3a.inst_num][clk - 1].setString("EX");
		}
	}
	else
	{
		buf7a.inputData(buf3a.RegWriteE, 0, buf3a.MemtoRegE, aluoutE1, WriteRegE1);
		if (clk > 3) {
			buf7a.setInstNum(buf3a.inst_num, buf3a.pc);
			if (buf3a.inst_num >= 0)
			g.stages[buf3a.inst_num][clk - 1].setString("EX");
		}
	}

	if (buf3b.MemtoRegE || buf3b.MemWriteE)
	{
		buf7b.clr();
		buf4.inputData(buf3b.RegWriteE, buf3b.MemtoRegE, buf3b.MemWriteE, aluoutE2, WriteDataE2, WriteRegE2);
		if (clk > 3) {
			buf4.setInstNum(buf3b.inst_num, buf3b.pc);
			if (buf3b.inst_num >= 0)
			g.stages[buf3b.inst_num][clk - 1].setString("EX");
		}
	}
	else
	{
		buf7b.inputData(buf3b.RegWriteE, 0, buf3b.MemtoRegE, aluoutE2, WriteRegE2);
		if (clk > 3) {
			buf7b.setInstNum(buf3b.inst_num, buf3b.pc);
			if (buf3b.inst_num >= 0)
			g.stages[buf3b.inst_num][clk - 1].setString("EX");
		}
	}
	if (!(buf3a.MemtoRegE || buf3a.MemWriteE) && !(buf3b.MemtoRegE || buf3b.MemWriteE))
	{
		buf4.setInstNum(-1, 0);
		buf4.inputData(0, 0, 0, 0, 0, 0);
		
	}

}
void muxforALUs()
{

	switch (h1.ForwardAE)
	{
	case 1:
	case 0:
		SrcAE1 = c.isComp(buf3a.RsE) ? c.find(buf3a.RsE) : buf3a.RD1E;
		break;
	case 2: SrcAE1 = buf4.ALUOutM;
		break;
	case 3: SrcAE1 = buf5.ALUOutM2;
		break;
	case 4: SrcAE1 = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	switch (h1.ForwardBE)
	{
	case 0:
	case 1:
		WriteDataE1 = c.isComp(buf3a.RtE) ? c.find(buf3a.RtE) : buf3a.RD2E;
		break;
	case 2: WriteDataE1 = buf4.ALUOutM;
		break;
	case 3: WriteDataE1 = buf5.ALUOutM2;
		break;
	case 4: WriteDataE1 = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	switch (h2.ForwardAE)
	{
	case 0:
	case 1:
		SrcAE2 = c.isComp(buf3b.RsE) ? c.find(buf3b.RsE) : buf3b.RD1E;
		break;
	case 2: SrcAE2 = buf4.ALUOutM;
		break;
	case 3: SrcAE2 = buf5.ALUOutM2;
		break;
	case 4: SrcAE2 = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}
	switch (h2.ForwardBE)
	{
	case 0:
	case 1:
		WriteDataE2 = c.isComp(buf3b.RtE) ? c.find(buf3b.RtE) : buf3b.RD2E;
		break;
	case 2: WriteDataE2 = buf4.ALUOutM;
		break;
	case 3: WriteDataE2 = buf5.ALUOutM2;
		break;
	case 4: WriteDataE2 = (buf6.MemtoRegM3) ? buf6.ReadDataM3 : buf6.ALUOutM3;
		break;
	default:
		break;
	}

	WriteRegE1 = (buf3a.RegDstE == 0) ? buf3a.RtE : buf3a.RdE;
	WriteRegE2 = (buf3b.RegDstE == 0) ? buf3b.RtE : buf3b.RdE;
	SrcBE1 = (buf3a.ALUSrcE == 0) ? WriteDataE1 : buf3a.SignImmE;
	SrcBE2 = (buf3b.ALUSrcE == 0) ? WriteDataE2 : buf3b.SignImmE;
}
void FlushUnit()
{
	if (h1.FlushE)
	{
		
		arr[buf2a.inst_num][1] = -1;
		buf2a.clr();

		arr[buf3b.inst_num][1] = -1;
		buf3b.flushE();
		
		arr[buf2b.inst_num][1] = -1;
		buf2b.clr();
	
		arr[buf1a.inst_num][1] = -1;
		buf1a.flush();
		arr[buf1b.inst_num][1] = -1;
		buf1b.flush();
		
	}
	if (h2.FlushE)
	{
		arr[buf1a.inst_num][1] = -1;
		arr[buf1b.inst_num][1] = -1;
		arr[buf2a.inst_num][1] = -1;
		arr[buf2b.inst_num][1] = -1;
	
		buf2a.clr();
		buf2b.clr();
		buf1a.flush();
		buf1b.flush();

	}
}
void intersectingStalls()
{
	stall1 = hs.isStall(cu1.RsD, buf3b.RtE, cu1.RtD, buf3b.MemtoRegE, cu1.branch, buf3b.RegWriteE, WriteRegE2);
	stall2 = hs.isStall(cu2.RsD, buf3a.RtE, cu2.RtD, buf3a.MemtoRegE, cu2.branch, buf3a.RegWriteE, WriteRegE2);
}
void handlePC()
{
	int h = 0;

	if (branchsignal == 1) {
		pcin1 = nextPC;
		pcin2 = pcin1 + 4;
	}
	else if (branchsignal == 2) {
		pcin1 = nextPC;
		pcin2 = pcin1 + 4;
	}
	else {
		int ya3 = nx.calculatenextPC(stck, h);
		if (ya3 == 1) {
			pcin1 = pcout1 + 8;
			pcin2 = pcin1 + 4;
		}
		else if (ya3 != 5 && ya3 != 6) {
			pcin1 = ya3;
			pcin2 = pcin1 + 4;
		}
		else if (ya3 == 5) {
			pcin1 = nx.boffset1;
			pcin2 = pcin1 + 4;
		}
		else if (ya3 == 6) {
			pcin1 = nx.boffset2;
			pcin2 = pcin1 + 4;
		}
	}

}