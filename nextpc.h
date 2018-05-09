#pragma once
#ifndef NEXTPC_H
#define NEXTPC_H
#include <stack>
#include "imem.h"
using namespace std;
class nextpc {

public:
	bool jumped;
	int jp1, jp2, b1, b2, jr1, jr2, ret1, ret2, jl1, jl2;
	unsigned int pcin1, pcin2,pcout1,pcout2;
	int jimm1, jimm2, boffset1, boffset2;
	unsigned int currentj1, currentjr1, currentreturn1, currentjal1, currentj2, currentjr2, currentreturn2, currentjal2;
	nextpc() {
		jumped = false;
	}

	void setInput(int jump1, int jump2, int branch1, int branch2, 
		int jumpr1, int jumpr2, int return1, int return2, int jal1,
		int jal2, unsigned int pc1, unsigned int pc2, int Jimm1, int Jimm2, int branchoffset1, int branchoffset2) {
		
		jimm1 = Jimm1;
		jimm2 = Jimm2;
		boffset1 = branchoffset1;
		boffset2 = branchoffset2;
		jp1 = jump1;
		jp2 = jump2;
		b1 = branch1;
		b2 = branch2;
		jr1 = jumpr1;
		jr2 = jumpr2;
		ret1 = return1;
		ret2 = return2;
		jl1 = jal2;
		jl2 = jal2;
		pcout1 = pc1;
		pcout2 = pc2;
	}

	unsigned int calculatenextPC(stack <unsigned int> &pc, int &h) {
		
		if (jp1) { h = 1;  return jimm1 * 4; }
		else if (jp2) { h = 2; return jimm2 * 4; }
		else if (jl1) {
			h = 1;  return jimm1 * 4;
		}
		else if (jl2) { h = 2;  return jimm2 * 4; }
		else if (ret1) {
			int top = -1;
			if (!pc.empty()) {
				top = pc.top();
				pc.pop();
				h = 1;
				return top;
			}
		}
		else if (ret2) {
			int top = -1;
			if (!pc.empty()) {
				top = pc.top();
				pc.pop();
				h = 2;
			}
			return top;
		}

		/*	else {
				h = 0; return 1;
			}*/
		else if (b1)
			return 5;
		else if (b2)
			return 6;
		else {
			h = 0;
			return 1;
		}

	}

	void setInsts(int inst1, int inst2,int pco1, int pco2) {
		if (inst1 >> 26 == 0x2)
			currentj1 = pco1;
		else if (inst2 >> 26 == 0x2)
			currentj2 = pco2;
		else if (inst1 >> 26 == 0x3)
			currentjal1= pco1;
		else if (inst2 >> 26 == 0x3)
			currentjal2 = pco2;
		else if (inst1 >> 26 == 0x5)
			currentjr1 = pco1;
		else if (inst2 >> 26 == 0x5)
			currentjr2 = pco2;
		//after getting the numinsts of these ones, then we attach them to the others.
	}

unsigned int predictBranch(BTB &b, unsigned int currentpc) {
		if (b.isBranch(currentpc)!=-1)
		{
			if (b.TakenorNot(currentpc))
				return b.predict[b.isBranch(currentpc)].predictedPC;
			else return -1;
		}
}

int correctPrediction(BTB &b, int actual, int predicted) {
	if (actual == predicted)
		return 0;
	if (actual != predicted) {
		if (actual == 1)
			//branch should be taken
			return 1;
		if (actual == 0)
			//branch should not be taken
			return 2;
	}
}

 int fixbranch(BTB &b, int actual, unsigned int bpc) {
	int state = correctPrediction(b, actual, b.TakenorNot(bpc));
	switch (state) {
	case 0:
		b.update(bpc, actual);
		return -1;
		break;
	case 1:
		b.update(bpc, 1);
		return b.predict[b.isBranch(bpc)].predictedPC;
		break;
	case 2:
		b.update(bpc, 0);
		return 3;
		break;
	default: break;
	}

}

};

#endif