#include "stdafx.h"
#include "stdio.h"
#undef __analysis_assume
#include <CodeAnalysis\SourceAnnotations.h>

#define BUF_SIZE 100
#define STR_SIZE 200

void zeroing();

_Ret_cap_(size) char *my_alloc(size_t size) {
	char *ch  = (char *)malloc(size);
	if (! ch) { // FIXED
		exit(-1);
	}
	*ch = NULL;
	ch[size-1] = NULL;  // null terminate here too, to be safe
	return ch;
}

HRESULT input(_Out_cap_c_(BUF_SIZE) [SA_Post(Tainted=SA_Yes)] char *buf) {
	return (fgets(buf, BUF_SIZE, stdin) != NULL)?SEVERITY_SUCCESS:SEVERITY_ERROR; // FIXED
}

_Ret_cap_c_(STR_SIZE) [returnvalue:SA_Post(Tainted=SA_Yes)] char *do_read() {
	char *buf = my_alloc(STR_SIZE);
	printf("Allocated a string at %p", buf); // FIXED
	if (FAILED(input(buf))) { // FIXED
		printf("error!");
		exit(-1);
	}
	if (*buf == NULL) // FIXED
		printf("empty string");
	return buf;
}

void copy_data([SA_Post(Tainted=SA_Yes)] _In_count_c_(BUF_SIZE) char *buf1,
               [SA_Post(Tainted=SA_Yes)] _Out_cap_c_(BUF_SIZE) char *buf2) {
	memcpy(buf2,buf1,BUF_SIZE); 
	buf2[BUF_SIZE-1] = NULL; // null terminate, just in case
}

int execute([SA_Pre(Tainted=SA_No)] char *buf) {
	return system(buf); // pass buf as command to be executed by the OS
}

void validate([SA_Pre(Tainted=SA_Yes)][SA_Post(Tainted=SA_No)] char *buf) {

    // This is a magical validation method, which turns tainted data
    // into untainted data, for which the code not shown.
    //
    // A real implementation might for example use a whitelist to filter
    // the string.

}

_Check_return_ int test_ready() {
	// code not shown
	return 1;
}

int APIENTRY WinMain(HINSTANCE hInstance, HINSTANCE hPrevInstance, LPSTR lpCmdLine, int nCmdShow) {
	char *buf1 = do_read();
	char *buf2 = my_alloc(BUF_SIZE);
	if (buf2 == NULL)
		exit(-1);
	zeroing();
	if (test_ready() != 1) { // FIXED
		exit(-1);
	}
	validate(buf1);
	execute(buf1);
        
        char* buf3 = do_read();
	copy_data(buf3, buf2); 
	validate(buf2);
	execute(buf2);

    char *buf4 = do_read();
	validate(buf4);
    execute(buf4);

}

// *****************************************************************

void zero(_Out_cap_(len) int *buf, int len)
{
    int i;
    for(i = 0; i < len; i++)
        buf[i] = 0;
}

void zeroboth(_Out_cap_(len) int *buf, int len, 
              _Out_cap_(len3) int *buf3, int len3)
{
    int *buf2 = buf;
    int len2 = len;
    zero(buf2, len2);
    zero(buf3, len3);
}

void zeroboth2(_Out_cap_(len) int *buf, int len, 
	       _Out_cap_(len3) int *buf3, int len3)
{
	zeroboth(buf, len3, buf3, len);
}

void zeroing()
{
    int elements[200];
    int oelements[100];
    zeroboth2(elements, 200, oelements, 100);
}
