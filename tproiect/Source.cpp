#include <Windows.h>
#include <CommCtrl.h>
#include <tchar.h>
#include "resource.h"
#include <stdio.h>
#include <stdlib.h>
#include <cstring>
using namespace std;
int gexp[512]; //tabel
int glog[256];
#define  prim = 0x11d;

int mult(int x, int y)//inmulteste 2 indici dar fara sa ii bage in gf de ....
{
	int z = 0;
	int i = 0;
	while (y >> i > 0)
	{
		if (y & (1 << i))
			z = z^x << i;
		i++;
	}
	return z;
}
int  length(int n)
{
	int bits = 0;
	while (n >> bits)
		bits += 1;
	return bits;
}
int diiv(int dividend, int divisor)
{


	int dl1 = length(dividend);
	int dl2 = length(divisor);
	if (dl1 < dl2)
		return dividend;

	for (int i = dl1 - dl2; i >= 0; i--)
	{
		if (dividend & (1 << i + dl2 - 1))
			dividend ^= divisor << i;
	}
	return dividend;
}

void log()
{
	int i, x;
	gexp[0] = 1;
	gexp[1] = 2;
	glog[1] = 0;
	glog[2] = 1;
	x = 2;
	for (i = 2; i < 255; i++)
	{
		x <<= 1;
		if (x & 0x100)
			x ^= 0x11d;

		gexp[i] = x; //anti log
		glog[x] = i; //log

	}
	for (i = 255; i <= 512; i++)
	{

		gexp[i] = gexp[i - 255];
	}

}
int gpow(int x, int  power)
{
	return gexp[(glog[x] * power) % 255];
}
int ginverse(int x)
{
	return gexp[255 - glog[x]];
}
int gmultylog(int x, int y)
{
	if (x == 0 || y == 0)
		return 0;

	return gexp[glog[x] + glog[y]];
}
int gdiv(int x, int y)
{

	if (x == 0)
		return 0;

	return gexp[(glog[x] + 255 - glog[y]) % 255];
}
int *gmultipolyscalar(int *p, int x, int c)
{
	int r[300];
	int i;
	for (i = 0; i < c; i++)
		r[i] = gmultylog(p[i], x);
	return r;
}
int *gpolyadd(int *p, int *q, int c, int m, int &z)
{
	int r[300];
	if (c > m)
		z = c;
	else
		z = m;
	for (int i = 0; i <= z; i++)
		r[i] = 0;
	int i;
	for (i = 0; i < c; i++)
		r[i + z - c] = p[i];
	for (i = 0; i < m; i++)
		r[i + z - m] ^= q[i];

	return r;
}
int * gmul(int *p, int * q, int c, int m, int &z)
{
	
	int r[300];
	z = c + m - 1;
	int j, i;
	for (i = 0; i <= z + 4; i++)
	{
		r[i] = 0;
	}


	for (j = 0; j < m; j++)
	{
		for (i = 0; i < c; i++)
			r[i + j] ^= gmultylog(p[i], q[j]);
											

	}
	return r;

}
int gpolyeval(int *poly, int c, int  x)
{

	int y = poly[0];
	int i;
	for (i = 1; i < c; i++)
		y = gmultylog(y, x) ^ poly[i];
	return y;
}
int *rsgenpoly(int nsym, int &c)
{
	int g[500];
	
	g[0] = 1;
	int *d;
	d = g;
	int z = 1;
	int i;
	int p;
	int l[3];
	for (i = 0; i < nsym; i++)
	{
		l[0] = gpow(2, i);
		l[1] = 1;
		d = gmul(g, l, z, 2, p);
		z = p;
		for (int j = 0; j <z; j++)
			g[j] = d[j];
	}
	c = z;
	return g;

}
int* gpolydiv(int *dividend, int *divisor, int n, int m, int ecc, int &p)
{
	int o = n;
	int g;
	int i, j;
	int aux[500];
	for (i = 0; i < m; i++)
	{
		aux[m - i - 1] = divisor[i];
	}
	for (i = 0; i < m; i++)
	{
		divisor[i] = aux[i];
	}
	int msg_out[500];

	for (i = 0; i < n; i++)
	{
		aux[i] = dividend[n - i - 1];
	}
	for (i = 0; i < n; i++)
	{
		dividend[i] = aux[i];
	}
	for (i = n; i <n + ecc; i++)
	{
		msg_out[i] = 0;
	}
	for (i = 0; i < n; i++)
	{
		msg_out[i] = dividend[i];
	}
	n = n + ecc;
	int coef;
	for (i = 0; i < n - m + 1; i++)
	{
		coef = msg_out[i];
		if (coef != 0)
			for (j = 1; j < m; j++)

				if (divisor[j] != 0)
					msg_out[i + j] ^= gmultylog(divisor[j], coef);

	}
	p = m - 1;
	i = 0;
	g = 0;
	while (msg_out[i] >= 0)
	{
		g++;
		i++;
	}
	p = g;
	return msg_out;//cat si rest

}
int *rscalsyndromes(int * msg, int y, int nsym)
{
	//'''Given the received codeword msg and the number of error correcting symbols (nsym), computes the syndromes polynomial.
	//Mathematically, it's essentially equivalent to a Fourrier Transform (Chien search being the inverse).
	//# Note the "[0] +" : we add a 0 coefficient for the lowest degree(the constant).This effectively shifts the syndrome, and will shift every computations depending on the syndromes(such as the errors locator polynomial, errors evaluator polynomial, etc.but not the errors positions).
	//# This is not necessary, you can adapt subsequent computations to start from 0 instead of skipping the first iteration(ie, the often seen range(1, n - k + 1)),
	int synd[100], i;
	for (i = 0; i < nsym; i++)
		synd[i] = 0;
	for (i = 0; i < nsym; i++)
	{
		synd[i] = gpolyeval(msg, y, gpow(2, i));

	}
	return synd; //# pad with one 0 for mathematical precision(else we can end up with weird calculations sometimes)
}
int * rsmsg(char *msg_in, int nsym)

{
	int l = 0;
	int i;
	int pa[500];
	//'''Reed-Solomon main encoding function'''
	int *gen = rsgenpoly(nsym, l);
	int c[500];
	for (i = 0; i < l; i++)
		pa[i] = gen[i];
	int h = strlen(msg_in);
	for (i = 0; i < strlen(msg_in); i++)
	{
		c[i] = (int)msg_in[i];
	}
	//# Pad the message, then divide it by the irreducible generator polynomial
	int remainder;
	int p;
	int *msg_out = gpolydiv(c, pa, h, l, l - 1, p);
	int msg[500];
	int f = 0;
	for (i = h - 1; i >= 0; i--)
	{
		msg[h - 1 - i] = c[i];
	}
	for (i = p - l + 1; i <p; i++)
	{

		msg[i + h - p + l - 1] = msg_out[i];
	}

	rscalsyndromes(msg, h + l - 1, nsym);

	for (i = 0; i<h; i++)
		printf("%d ", msg[i]);
	for (i = h; i < h + l - 1; i++)
	{
		printf("%d ", msg[i]);
	}


	return 0;
}
#pragma comment(linker, \
  "\"/manifestdependency:type='Win32' "\
  "name='Microsoft.Windows.Common-Controls' "\
  "version='6.0.0.0' "\
  "processorArchitecture='*' "\
  "publicKeyToken='6595b64144ccf1df' "\
  "language='*'\"")

#pragma comment(lib, "ComCtl32.lib")
int c = 0, d = 0;
TCHAR text[255];

LPTSTR  edittxt;
LPCTSTR lpString;
INT_PTR CALLBACK DialogProc(HWND hDlg, UINT uMsg, WPARAM wParam, LPARAM lParam)
{
	HINSTANCE g=NULL;
	HMENU hMenu;
	
	switch (uMsg)
	{
		
		
	
	case WM_COMMAND:
		switch (LOWORD(wParam))
		{
		case ID_DESPRE_DESPRE:
		{
			MessageBox(hDlg, "", "Informatii", 0);
		}
		case ID_TIPULDEDATE_TEXT:
		{
			c = 1;
			break;
		}
		case ID_TIPULDEDATE_NUMERE:
		{
			c = 2;
			break;
		}
		case ID_TIPULDEDATE_COMBINATIEDETEXTSINUMERE:
		{
			c = 0;
			break;
		}
		case ID_TIPULOPERATIEI_DECODARE:
		{
			d = 1;
			break;
		}
		case ID_TIPULOPERATIEI_CODARE:
		{
			d = 0;
			break;
		}
		case IDC_BUTTON1:
		{

			GetDlgItemText(hDlg, IDC_EDIT1, text, 255);
			MessageBox(hDlg, text, "edit text", 0);
		}
		case IDCANCEL:
			SendMessage(hDlg, WM_CLOSE, 0, 0);
			return TRUE;
		}
		
		break;

	case WM_CLOSE:
		if (MessageBox(hDlg, TEXT(" Doriti sa inchideti programul?"), TEXT("Inchidere"),
			MB_ICONQUESTION | MB_YESNO) == IDYES)
		{
			DestroyWindow(hDlg);
		}
		return TRUE;

	case WM_DESTROY:
		PostQuitMessage(0);
		return TRUE;
	}

	return FALSE;
}

int WINAPI _tWinMain(HINSTANCE hInst, HINSTANCE h0, LPTSTR lpCmdLine, int nCmdShow)
{
	HWND hDlg;
	MSG msg;
	BOOL ret;

	InitCommonControls();
	hDlg = CreateDialogParam(hInst, MAKEINTRESOURCE(IDD_DIALOG1), 0, DialogProc, 0);
	ShowWindow(hDlg, nCmdShow);

	while ((ret = GetMessage(&msg, 0, 0, 0)) != 0) {
		if (ret == -1)
			return -1;

		if (!IsDialogMessage(hDlg, &msg)) {
			TranslateMessage(&msg);
			DispatchMessage(&msg);
		}
	}

	return 0;
}