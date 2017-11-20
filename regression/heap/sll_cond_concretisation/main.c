#include <stdlib.h>
#include <assert.h>

extern int __VERIFIER_nondet_int(void);

struct list{
	struct list* next;
};

int main()
{
	struct list *p,*q;
	p = malloc(sizeof(struct list));
	
	while(__VERIFIER_nondet_int) {
		q = p;
		p = malloc(sizeof(struct list));
		q->next = p;
		assert(q->next != NULL);
		p = q;
		if (p->next == NULL)
			assert(0);
		p = p->next;
		assert(p != NULL);
		p->next = NULL;
	}

	return 0;
}
