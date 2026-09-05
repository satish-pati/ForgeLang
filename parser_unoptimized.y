
%{
#include<stdio.h>
extern int yylineno;  /* Line number from lexer */
#include<string.h>
#include<stdlib.h>
#include<ctype.h>
#include<float.h>
#include<math.h>
extern FILE *yyin;
extern char buffer[];
char err[32768];
int e=0;
int label=0;
char* genvar();
void printQuadruples();
char imcode[10000][10000];
int code=0;
int offset=0;
int saveoffset;
int string_count = 0;


#define FOR_STASH_DEPTH 16
#define FOR_STASH_SLOTS 64
static char for_incr_stash[FOR_STASH_DEPTH][FOR_STASH_SLOTS][10000];
static int is_ref_param(int func_start_idx, const char *varname);
static int  for_incr_count[FOR_STASH_DEPTH];
static int  for_incr_sp = 0;  /* stack pointer: next free slot */



/* ── Enum constant table ── */
#define ENUM_TABLE_SIZE 256
typedef struct EnumEntry {
    char name[100];
    int  value;
    struct EnumEntry* next;
} EnumEntry;
static EnumEntry* enum_table[ENUM_TABLE_SIZE];

static unsigned int enum_hash(const char* key) {
    unsigned int h = 0;
    while (*key) h = (h << 5) + *key++;
    return h % ENUM_TABLE_SIZE;
}

void enum_put(const char* name, int value) {
    unsigned int idx = enum_hash(name);
    EnumEntry* e2 = malloc(sizeof(EnumEntry));
    strcpy(e2->name, name);
    e2->value = value;
    e2->next = enum_table[idx];
    enum_table[idx] = e2;
}


int enum_get(const char* name, int* out_value) {
    unsigned int idx = enum_hash(name);
    EnumEntry* e2 = enum_table[idx];
    while (e2) {
        if (strcmp(e2->name, name) == 0) { *out_value = e2->value; return 1; }
        e2 = e2->next;
    }
    return 0;
}

int is_enum_constant(const char* name) {
    int dummy;
    return enum_get(name, &dummy);
}

int _enum_next_val = 0;  /* running counter for auto-valued enum members */

int loop_depth = 0;
int switch_depth = 0;

char current_function[100] = "";
char current_return_type[100] = "";
int in_function = 0;
int has_return_statement = 0;

typedef struct Param{
    char name[100];
    char type[100];
    int  is_ref;   /* 1 if declared with '@' (pass-by-reference); set at registration time
                      before the '@' is stripped from type — do NOT rely on type[0]=='@' */
    struct Param* next;
} Param;
typedef struct BasicBlock {
    int start_line;
    int end_line;
    int block_id;
    struct BasicBlock* next;
} BasicBlock;

BasicBlock* blocks = NULL;
int block_count = 0;


char current_switch_var[100];
typedef struct Function{
    char name[100];
    char return_type[100];
    Param* params;
    int param_count;
    int start_label;
    struct Function* next;
} Function;




Function* func_list = NULL;

Param* createParam(char* name, char* type){
    Param* p = (Param*)malloc(sizeof(Param));
    strcpy(p->name, name);
    strcpy(p->type, type);
    p->is_ref = 0;
    p->next = NULL;
    return p;
}

Function* createFunction(char* name, char* ret_type){
    Function* f = (Function*)malloc(sizeof(Function));
    strcpy(f->name, name);
    strcpy(f->return_type, ret_type);
    f->params = NULL;
    f->param_count = 0;
    f->next = NULL;
    return f;
}

void addFunction(Function* f){
    f->next = func_list;
    func_list = f;
}

Function* findFunction(char* name){
    Function* temp = func_list;
    while(temp){
        if(strcmp(temp->name, name) == 0) return temp;
        temp = temp->next;
    }
    return NULL;
}

typedef struct Symbol{
        char name[100];
        char type[100];
        int size;
        int offset;
        int dimensions[10];
        int dim_count;
        int decl_line;   /* source line number where this variable was declared */
        struct Symbol*next;
} Symbol;

struct Type{
        char str[1000];
        int size;
};

struct Decl{
        char key[1000];
        char type[1000];
        char lt[100];
        char op[100];
        int size;
        int is_literal;
        int re;
        int str_len;
        struct Decl* next;
};

struct Node{
        struct Node* next;
        int addr;
};
struct Expr{
        char str[1000];
        char type[100];
        int lv;
        int str_len;
        int is_deref;        /* 1 if this expr was produced by 'deref VAR' */
        char deref_src[100]; /* the pointer variable name when is_deref==1  */
        struct Expr* next;
};
struct BoolNode{
        struct Node* T;
        struct Node* F;
        struct Node* N;
        struct Node* B;
        struct Node* C;
};
struct Subscript{
        char indices[1000];
        int count;
};

struct Node* createNode(int addr){
        struct Node* node = (struct Node*)malloc(sizeof(struct Node));
        node->next = NULL;
        node->addr = addr;
        return node;
}

struct Decl* createDecl(char* key){
        struct Decl *node = (struct Decl*)malloc(sizeof(struct Decl));
        node->re=0;
        node->is_literal=0;  
        strcpy(node->key,key);
        return node;
}

struct Expr* createExpr(){
    struct Expr* e = (struct Expr*)malloc(sizeof(struct Expr));
    memset(e, 0, sizeof(struct Expr));
    e->next = NULL;
    e->str_len = 0;
    e->lv = 0;
    e->is_deref = 0;
    e->deref_src[0] = '\0';
    return e;
}

struct Type* createType(){
        return (struct Type*)malloc(sizeof(struct Type));
}

struct BoolNode* createBoolNode(){
        struct BoolNode* node = (struct BoolNode*)malloc(sizeof(struct BoolNode));
    node->T = NULL;
    node->F = NULL;
    node->N = NULL;
    node->B = NULL;
    node->C = NULL;
    return node;
}
struct Subscript* createSubscript(){
        struct Subscript* node = (struct Subscript*)malloc(sizeof(struct Subscript));
        strcpy(node->indices, "");
        node->count = 0;
        return node;
}
struct Node* merge(struct Node* a,struct Node* b){
        if (a==NULL && b==NULL) return NULL;
        if (a==NULL) return b;
        if (b==NULL) return a;
        struct Node* t = a;
        while(t->next!=NULL){
                t = t->next;
        }
        t->next = b;
        return a;
}

int checkfloat(char* t){
        while(*t){
                if (*t=='.') return 1;
                t++;
        }
        return 0;
}

void backpatch(struct Node* a,int addr){
        while(a!=NULL){
                int len = strlen(imcode[a->addr]);
                if (imcode[a->addr][len-1] != '\n') {
                    sprintf(imcode[a->addr] + len, "%d\n", addr);
                }
                a = a->next;
        }
}

int isNumericConstant(char* str) {
    if (!str || *str == '\0') return 0;
    char* ptr = str;
    if (*ptr == '-' || *ptr == '+') ptr++;
    int has_digit = 0;
    int has_dot = 0;
    while (*ptr) {
        if (isdigit(*ptr)) has_digit = 1;
        else if (*ptr == '.' && !has_dot) has_dot = 1;
        else return 0;
        ptr++;
    }
    return has_digit;
}

int isFloatingType(char* type){
    return (strcmp(type, "float") == 0 || strcmp(type, "double") == 0);
}

int isIntegerType(char* type){
    return (strcmp(type, "char") == 0 || 
            strcmp(type, "short") == 0 || 
            strcmp(type, "int") == 0 || 
            strcmp(type, "long") == 0 ||
            strcmp(type, "const int") == 0);
}

char* getBaseType(char* type_str) {
    static char base[100];
    
    // Strip "const " prefix if present
    char* actual_type = type_str;
    if (strncmp(type_str, "const ", 6) == 0) {
        actual_type = type_str + 6;
    }
    
    // Handle array types
    char* bracket = strchr(actual_type, '[');
    if (bracket) {
        int len = bracket - actual_type;
        strncpy(base, actual_type, len);
        base[len] = '\0';
        return base;
    }
    return actual_type;
}
int getTypeRank(char* type){
    if (strcmp(type, "char") == 0) return 1;
    if (strcmp(type, "short") == 0) return 2;
    if (strcmp(type, "int") == 0) return 3;
    if (strcmp(type, "const int") == 0) return 3;
    if (strcmp(type, "long") == 0) return 4;
    if (strcmp(type, "float") == 0) return 5;
    if (strcmp(type, "const float") == 0) return 5;
    if (strcmp(type, "double") == 0) return 6;
    if (strcmp(type, "const double") == 0) return 6;
    return 0;
}


char* promoteType(char* t1, char* t2){
    if (strcmp(t1, t2) == 0) return t1;
    int rank1 = getTypeRank(t1);
    int rank2 = getTypeRank(t2);
    return (rank1 > rank2) ? t1 : t2;
}


// Check if types are compatible for return
int isTypeCompatible(char* expected, char* actual) {
    // Remove const qualifier for comparison
    char exp_clean[100], act_clean[100];
    strcpy(exp_clean, expected);
    strcpy(act_clean, actual);
    
    if(strncmp(exp_clean, "const ", 6) == 0) {
        strcpy(exp_clean, exp_clean + 6);
    }
    if(strncmp(act_clean, "const ", 6) == 0) {
        strcpy(act_clean, act_clean + 6);
    }
    
    // Get base types (without array dimensions)
    char* exp_base = getBaseType(exp_clean);
    char* act_base = getBaseType(act_clean);

    /* Pointer types: only genuine ptr: prefixes are pointers.
       "char*" is an internal tag for string literals — not a user pointer.
       ptr:T ← ptr:T: compatible. ptr:T ← non-ptr or vice-versa: incompatible.
       ptr:T ← ptr:U where T≠U: warn (matches assignment/call-arg behaviour). */
    int exp_is_ptr = (strncmp(exp_base, "ptr:", 4) == 0);
    int act_is_ptr = (strncmp(act_base, "ptr:", 4) == 0);
    if (exp_is_ptr || act_is_ptr) {
        if (!exp_is_ptr || !act_is_ptr) return 0;  /* ptr ↔ non-ptr: incompatible */
        /* ptr:T ↔ ptr:U — allow but warn if pointee types differ */
        if (strcmp(exp_base, act_base) != 0) {
            sprintf(err+strlen(err),
                "Line %d: Warning: pointer type mismatch in return: "
                "returning '%s' where '%s' expected\n",
                yylineno, act_base, exp_base);
        }
        return 1;
    }
    
    // Exact match
    if (strcmp(exp_base, act_base) == 0) return 1;
    
    // Get type ranks
    int exp_rank = getTypeRank(exp_base);
    int act_rank = getTypeRank(act_base);
    
    // Both are numeric types - allow conversion
    if (exp_rank > 0 && act_rank > 0) {
        // Issue warnings for problematic conversions
        if (act_rank > exp_rank) {
            // Narrowing conversion
            sprintf(err+strlen(err), 
                "Warning: Implicit narrowing conversion from %s to %s\n",
                act_base, exp_base);
        }
        
        // Float to integer conversion loses precision
        if (isFloatingType(act_base) && isIntegerType(exp_base)) {
            sprintf(err+strlen(err), 
                "Warning: Conversion from %s to %s may lose precision\n",
                act_base, exp_base);
        }
        
        // Integer to float is usually safe but mention it
        if (isIntegerType(act_base) && isFloatingType(exp_base)) {
            // This is generally safe, no warning needed for promotion
        }
        
        return 1;  // Allow all numeric conversions
    }
    
    // Not compatible
    return 0;
}




void validateNumericLiteral(char* literal, char* target_type, char* var_name) {
    if (!isNumericConstant(literal)) return;

    double value = atof(literal);

    if (strcmp(target_type, "char") == 0) {
        if (value < -128 || value > 127)
            sprintf(err+strlen(err),
                "Warning: Initializer %.0f for '%s' exceeds char range [-128, 127]\n",
                value, var_name);
    }
    else if (strcmp(target_type, "short") == 0) {
        if (value < -32768 || value > 32767)
            sprintf(err+strlen(err),
                "Warning: Initializer %.0f for '%s' exceeds short range [-32768, 32767]\n",
                value, var_name);
    }
    else if (strcmp(target_type, "int") == 0) {
        if (value < -2147483648.0 || value > 2147483647.0)
            sprintf(err+strlen(err),
                "Warning: Initializer %.0f for '%s' exceeds int range [-2147483648, 2147483647]\n",
                value, var_name);
    }
    else if (strcmp(target_type, "long") == 0) {
        if (value > 9223372036854775807.0 || value < -9223372036854775808.0)
            sprintf(err+strlen(err),
                "Warning: Initializer %.0f for '%s' exceeds long range\n",
                value, var_name);
    }
    else if (strcmp(target_type, "float") == 0) {
        if (value > FLT_MAX || value < -FLT_MAX) {
            sprintf(err+strlen(err),
                "Warning: Initializer %g for '%s' exceeds float range [-%g, %g] (will be inf)\n",
                value, var_name, FLT_MAX, FLT_MAX);
        } else if (value != 0.0 && fabs(value) < FLT_MIN) {
            sprintf(err+strlen(err),
                "Warning: Initializer %g for '%s' is too small for float (will underflow to 0)\n",
                value, var_name);
        }
    }
    else if (strcmp(target_type, "double") == 0) {
        if (isinf(value) || (value > DBL_MAX || value < -DBL_MAX)) {
            sprintf(err+strlen(err),
                "Warning: Initializer for '%s' exceeds double range (will be inf)\n",
                var_name);
        } else if (value != 0.0 && fabs(value) < DBL_MIN) {
            sprintf(err+strlen(err),
                "Warning: Initializer %g for '%s' is too small for double (will underflow to 0)\n",
                value, var_name);
        }
    }
}

/*duplicate parameter name check*/
int checkDuplicateParams(struct Decl* params) {
    struct Decl* p1 = params;
    while(p1) {
        struct Decl* p2 = p1->next;
        while(p2) {
            if(strcmp(p1->key, p2->key) == 0) return 1;
            p2 = p2->next;
        }
        p1 = p1->next;
    }
    return 0;
}

int tryConstantFold(struct Expr* op1, struct Expr* op2, char op, struct Expr* result) {
    if (!isNumericConstant(op1->str) || !isNumericConstant(op2->str)) return 0;
    double val1, val2, res;
    val1 = atof(op1->str);
    val2 = atof(op2->str);
    switch(op) {
        case '+': res = val1 + val2; break;
        case '-': res = val1 - val2; break;
        case '*': res = val1 * val2; break;
        case '/': if (val2 == 0) return 0; res = val1 / val2; break;
        case '%':
            if (val2 == 0) return 0;
            if (isFloatingType(op1->type) || isFloatingType(op2->type)) return 0;
            res = (int)val1 % (int)val2; break;
        case '&': res = (int)val1 & (int)val2; break;
        case '|': res = (int)val1 | (int)val2; break;
        case '^': res = (int)val1 ^ (int)val2; break;
        case 'l': res = (int)val1 << (int)val2; break;
        case 'r': res = (int)val1 >> (int)val2; break;
        default: return 0;
    }
    if(op=='&'||op=='|'||op=='^'||op=='>>'||op=='<<'){
        sprintf(result->str, "%d", (int)res);
        strcpy(result->type, "int");
    } else if (isFloatingType(op1->type) || isFloatingType(op2->type)) {
        sprintf(result->str, "%g", res);
        strcpy(result->type, "float");
    } else {
        /* int op int → always int (C semantics: truncate toward zero) */
        sprintf(result->str, "%d", (int)res);
        strcpy(result->type, "int");
    }
    result->lv = 0;
    return 1;
}

Symbol* createSymbol(char* name){
        Symbol* node = (Symbol*)malloc(sizeof(Symbol));
        memset(node, 0, sizeof(Symbol));
        strcpy(node->name,name);
        node->decl_line = yylineno;  /* capture source line at declaration time */
        return node;
}

typedef struct Env {
    struct Env* prev;
    int prev_offset;
    struct Table* table;
} Env;

Env* envs[1000];
int env_count = 0;

typedef struct TableEntry {
    char* key;
    Symbol* value;
    struct TableEntry* next;
} TableEntry;

typedef struct Table {
    TableEntry** buckets;
    int size;
} Table;

#define TABLE_SIZE 501
unsigned int hash(const char* key) {
    unsigned int hash = 0;
    while (*key) {
        hash = (hash << 5) + *key++;
    }
    return hash % TABLE_SIZE;
}

Table* create_table() {
    Table* table = malloc(sizeof(Table));
    table->buckets = calloc(TABLE_SIZE, sizeof(TableEntry*));
    table->size = TABLE_SIZE;
    return table;
}

void put(Table* table, const char* key, Symbol* sym) {
    unsigned int index = hash(key);
    TableEntry* new_entry = malloc(sizeof(TableEntry));
    new_entry->key = strdup(key);
    new_entry->value = sym;
    new_entry->next = table->buckets[index];
    table->buckets[index] = new_entry;
}

Symbol* get(Table* table, const char* key) {
    unsigned int index = hash(key);
    TableEntry* entry = table->buckets[index];
    while (entry) {
        if (strcmp(entry->key, key) == 0) return entry->value;
        entry = entry->next;
    }
    return NULL;
}

Env* create_env(Env* prev,int offset) {
    Env* env = malloc(sizeof(Env));
    env->prev = prev;
    env->table = create_table();
    env->prev_offset = offset;
    envs[env_count++] = env;
    return env;
}

void env_put(Env* env, const char* key, Symbol* sym) {
    put(env->table, key, sym);
}

Symbol* env_get(Env* env, const char* key) {
    for (Env* e = env; e != NULL; e = e->prev) {
        Symbol* found = get(e->table, key);
        if (found != NULL) return found;
    }
    return NULL;
}

Env* top = NULL;
/*
void print_table(Table* table) {
    for (int i = 0; i < table->size; i++) {
        TableEntry* entry = table->buckets[i];
        while (entry) {
                        printf("%-10d %-25s %-20s\n", 
                entry->value->offset, 
                entry->value->name, 
                entry->value->type);

            entry = entry->next;
        }
    }
}

void print_all_envs() {
    printf("\n=== Symbol Table (Storage Layout) ===\n");
    for (int i = 0; i < env_count; i++) {
        printf("\nScope %d:\n", i);
        printf("%-10s %-25s %-20s\n", "Offset", "Name", "Type");
printf("-----------------------------------------------\n");
        print_table(envs[i]->table);
    }
    printf("======================================\n");
}

*/




/* Return byte-size of a base type */
static int type_byte_size(const char* base) {
    if (strcmp(base,"char"  )==0) return 1;
    if (strcmp(base,"short" )==0) return 2;
    if (strcmp(base,"int"   )==0) return 4;
    if (strcmp(base,"float" )==0) return 4;
    if (strcmp(base,"long"  )==0) return 8;
    if (strcmp(base,"double")==0) return 8;
    return 4; /* default */
}

/* Extract base type from "int[5]" → "int", "char[2][3]" → "char", "int" → "int" */
static void extract_base(const char* full_type, char* out) {
    strcpy(out, full_type);
    char* bracket = strchr(out, '[');
    if (bracket) *bracket = '\0';
    /* strip leading @ if present */
    if (out[0] == '@') memmove(out, out+1, strlen(out));
}


/* Collect all symbols from a table into a sorted array (by offset) */
#define MAX_SYMS 512
static int collect_symbols(Table* table, Symbol** out) {
    int n = 0;
    for (int i = 0; i < table->size && n < MAX_SYMS; i++) {
        TableEntry* e = table->buckets[i];
        while (e && n < MAX_SYMS) { out[n++] = e->value; e = e->next; }
    }
    /* insertion sort by offset */
    for (int i = 1; i < n; i++) {
        Symbol* key = out[i]; int j = i-1;
        while (j >= 0 && out[j]->offset > key->offset) { out[j+1]=out[j]; j--; }
        out[j+1] = key;
    }
    return n;
}





void print_table(Table* table, FILE* out) {
    Symbol* syms[MAX_SYMS];
    int n = collect_symbols(table, syms);
    for (int i = 0; i < n; i++) {
        Symbol* s = syms[i];
        char base[100]; extract_base(s->type, base);
        int elem_size = type_byte_size(base);
        int total_elems = 1;
        for (int d = 0; d < s->dim_count; d++) total_elems *= s->dimensions[d];
        int total_bytes = elem_size * (total_elems > 0 ? total_elems : 1);

        /* Build dimension string e.g. "[3][4]" or "" */
        char dim_str[100] = "";
        if (s->dim_count > 0) {
            for (int d = 0; d < s->dim_count; d++) {
                char part[20]; sprintf(part, "[%d]", s->dimensions[d]);
                strcat(dim_str, part);
            }
        } else if (strchr(s->type, '[') != NULL) {
            /* fallback: pull dims from type string */
            char* p = strchr(s->type, '[');
            strcpy(dim_str, p ? p : "");
        }

        /* Category */
        char category[20];
        if (s->dim_count > 1)       strcpy(category, "multi-dim array");
        else if (s->dim_count == 1) strcpy(category, "array");
        else if (strchr(s->type,'[') != NULL) strcpy(category, "array");
        else                        strcpy(category, "scalar");

        /* merge base + dim_str into one type field */
        char full_type[100];
        snprintf(full_type, sizeof(full_type), "%s%s", base, dim_str);

        fprintf(out, "  %-8d  %-20s  %-20s  %-8d  %-8d  %-16s\n",
            s->offset,
            s->name,
            full_type,
            elem_size,
            total_bytes,
            category);
    }
}
void print_all_envs(FILE* out) {
    /* Count non-empty scopes */
    int non_empty = 0;
    for (int i = 0; i < env_count; i++) {
        for (int b = 0; b < envs[i]->table->size; b++) {
            if (envs[i]->table->buckets[b]) { non_empty++; break; }
        }
    }

    fprintf(out, "\n");
    fprintf(out, "==================================================================================\n");
    fprintf(out, "                        SYMBOL TABLE  (Storage Layout)                      \n");
    fprintf(out, "==================================================================================\n");

    int scope_printed = 0;
    for (int i = 0; i < env_count; i++) {
        /* Check if scope has any symbols */
        int has_syms = 0;
        for (int b = 0; b < envs[i]->table->size; b++)
            if (envs[i]->table->buckets[b]) { has_syms = 1; break; }

        char scope_label[50];
            fprintf(out, "\n");

        if (i == 0) strcpy(scope_label, "Global");
        else        sprintf(scope_label, "Local (scope %d)", i);

        fprintf(out, "  Scope %d  [%s]\n", i, scope_label);
        fprintf(out, "  %-8s  %-20s  %-20s  %-8s  %-8s  %-16s\n",
               "Offset", "Name", "Type", "ESize", "Total", "Category");
        fprintf(out, "  %-8s  %-20s  %-20s  %-8s  %-8s  %-16s\n",
               "--------", "--------------------", "--------------------",
               "--------", "--------", "----------------");

        if (!has_syms) {
            fprintf(out, "  (no symbols)\n");
        } else {
            print_table(envs[i]->table, out);
        }
        scope_printed++;
    }

    /* Grand total */
    int total_vars = 0;
    int total_bytes = 0;
    for (int i = 0; i < env_count; i++) {
        for (int b = 0; b < envs[i]->table->size; b++) {
            TableEntry* e = envs[i]->table->buckets[b];
            while (e) {
                Symbol* s = e->value;
                char base[100]; extract_base(s->type, base);
                int elem_size = type_byte_size(base);
                int total_elems = 1;
                for (int d = 0; d < s->dim_count; d++) total_elems *= s->dimensions[d];
                total_bytes += elem_size * (total_elems > 0 ? total_elems : 1);
                total_vars++;
                e = e->next;
            }
        }
    }
                fprintf(out, "\n");

    fprintf(out, "==================================================================================\n");
    fprintf(out, "  Total symbols: %d  |  Total storage: %d bytes\n", total_vars, total_bytes);
        fprintf(out, "==================================================================================\n");


}




char* calculateArrayOffset(Symbol* sym, struct Subscript* sub, char* base_name) {
    if (sym->dim_count == 0) return base_name;

    char indices_copy[1000];
    strcpy(indices_copy, sub->indices);
    char* idx_list[10];
    int idx_count = 0;

    char* ptr = indices_copy;
    while (*ptr) {
        if (*ptr == '[') {
            ptr++;
            idx_list[idx_count++] = ptr;
            while (*ptr && *ptr != ']') ptr++;
            if (*ptr == ']') *ptr = '\0';
            ptr++;
        } else {
            ptr++;
        }
    }

    if (idx_count > sym->dim_count) {
        e = 1;
        sprintf(err+strlen(err), "Too many subscripts for array %s\n", base_name);
        return genvar();
    }

    int elem_size = 4;
    if (strstr(sym->type, "char") != NULL) 
        elem_size = 1;
    else if (strstr(sym->type, "short") != NULL) 
        elem_size = 2;
    else if (strstr(sym->type, "int") != NULL || strstr(sym->type, "float") != NULL) 
        elem_size = 4;
    else if (strstr(sym->type, "long") != NULL || strstr(sym->type, "double") != NULL) 
        elem_size = 8;

    int all_constant = 1;
    for (int i = 0; i < idx_count; i++) {
        if (!isNumericConstant(idx_list[i])) { all_constant = 0; break; }
    }

    if (all_constant && sym->dim_count == 1) {
        int idx = atoi(idx_list[0]);
        /*  bounds check for constant index  */
        if (idx < 0) {
            e = 1;
            sprintf(err+strlen(err), "Array index %d is negative for array %s\n", idx, base_name);
        } else if (idx >= sym->dimensions[0] && sym->dimensions[0] > 0) {
            e = 1;
            sprintf(err+strlen(err), "Array index %d out of bounds for array %s[%d] (valid range: 0-%d)\n",
                    idx, base_name, sym->dimensions[0], sym->dimensions[0]-1);
        }
        int byte_offset = idx * elem_size;
        char* result = genvar();
        sprintf(result, "%d", byte_offset);
        return result;
    }

    if (all_constant && sym->dim_count > 1) {
        /*  multi-dim bounds check */
        for (int i = 0; i < idx_count && i < sym->dim_count; i++) {
            int idx = atoi(idx_list[i]);
            if (idx < 0) {
                e = 1;
                sprintf(err+strlen(err), "Index %d at dimension %d is negative for array %s\n", idx, i, base_name);
            } else if (idx >= sym->dimensions[i] && sym->dimensions[i] > 0) {
                e = 1;
                sprintf(err+strlen(err), "Index %d out of bounds at dimension %d for array %s (valid: 0-%d)\n",
                        idx, i, base_name, sym->dimensions[i]-1);
            }
        }
        int total_offset = 0;
        int multiplier = 1;
        for (int i = sym->dim_count - 1; i >= 0; i--) {
            if (i < idx_count) {
                int idx = atoi(idx_list[i]);
                total_offset += idx * multiplier;
            }
            if (i > 0) multiplier *= sym->dimensions[i];
        }
        total_offset *= elem_size;
        char* result = genvar();
        sprintf(result, "%d", total_offset);
        return result;
    }

    char* result = genvar();
    if (sym->dim_count == 1) {
        sprintf(imcode[code], "%d %s = %s * %d\n", code, result, idx_list[0], elem_size);
        code++;
        return result;
    }

    char* running_offset = genvar();
    sprintf(imcode[code], "%d %s = %s\n", code, running_offset, idx_list[0]);
    code++;

    for (int i = 1; i < idx_count; i++) {
        int multiplier = 1;
        for (int j = i; j < sym->dim_count; j++) multiplier *= sym->dimensions[j];
        char* temp1 = genvar();
        sprintf(imcode[code], "%d %s = %s * %d\n", code, temp1, running_offset, multiplier);
        code++;
        char* temp2 = genvar();
        sprintf(imcode[code], "%d %s = %s + %s\n", code, temp2, temp1, idx_list[i]);
        code++;
        strcpy(running_offset, temp2);
    }

    sprintf(imcode[code], "%d %s = %s * %d\n", code, result, running_offset, elem_size);
    code++;
    return result;
}

int isLiteral(char* str) {
    if (!str || *str == '\0') return 0;
    
    // Handle character literals: 'a', 'b', '\n', etc.
    if (str[0] == '\'' && strlen(str) >= 3 && str[strlen(str)-1] == '\'') {
        return 1;
    }
    
    // Handle casted constants: (type) value
    if (str[0] == '(') {
        char* closing = strchr(str, ')');
        if (closing) {
            char* value_part = closing + 1;
            while (*value_part == ' ') value_part++;
            return isLiteral(value_part);  // Recursive check on the value part
        }
    }
    
    // Handle numeric literals: 123, -45, 3.14, .5
    return (isdigit(str[0]) || 
            (str[0] == '-' && isdigit(str[1])) || 
            (str[0] == '.' && isdigit(str[1])));
}


int checkLiteralRange(char* literal, char* target_type) {
    if (!isNumericConstant(literal)) return 1;

    double value = atof(literal);
    int has_warning = 0;

    if (strcmp(target_type, "char") == 0) {
        if (value < -128 || value > 127) {
            sprintf(err+strlen(err),
                "Warning: Value %.0f out of range for char (valid range: -128 to 127)\n", value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "short") == 0) {
        if (value < -32768 || value > 32767) {
            sprintf(err+strlen(err),
                "Warning: Value %.0f out of range for short (valid range: -32768 to 32767)\n", value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "int") == 0) {
        if (value < -2147483648.0 || value > 2147483647.0) {
            sprintf(err+strlen(err),
                "Warning: Value %.0f out of range for int (valid range: -2147483648 to 2147483647)\n", value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "long") == 0) {
        if (fabs(value) > 9.223372e18) {
            sprintf(err+strlen(err),
                "Warning: Value %.0f may be out of range for long\n", value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "float") == 0) {
        if (value > FLT_MAX || value < -FLT_MAX) {
            sprintf(err+strlen(err),
                "Warning: Value %g exceeds float range [-%g, %g] (will be inf)\n",
                value, FLT_MAX, FLT_MAX);
            has_warning = 1;
        } else if (value != 0.0 && fabs(value) < FLT_MIN) {
            sprintf(err+strlen(err),
                "Warning: Value %g is too small for float (will underflow to 0)\n",
                value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "double") == 0) {
        if (isinf(value) || value > DBL_MAX || value < -DBL_MAX) {
            sprintf(err+strlen(err),
                "Warning: Value %g exceeds double range (will be inf)\n",
                value);
            has_warning = 1;
        } else if (value != 0.0 && fabs(value) < DBL_MIN) {
            sprintf(err+strlen(err),
                "Warning: Value %g is too small for double (will underflow to 0)\n",
                value);
            has_warning = 1;
        }
    }

    return !has_warning;
}

/* Returns 1 if the type string represents any pointer type.
   Handles both "ptr:T" (user-declared pointer)  */
int isPointerType(const char* type) {
    if (!type) return 0;
    return (strncmp(type, "ptr:", 4) == 0);
}

/* Normalise "char*" → "ptr:char" so both representations unify in type checks.
   Writes into out (must be at least 100 bytes). Returns out. */
char* normalizeType(const char* type, char* out) {
    if (strcmp(type, "char*") == 0) { strcpy(out, "ptr:char"); return out; }
    strncpy(out, type, 99); out[99] = '\0';
    return out;
}

/* Check for narrowing conversions between types */
int isNarrowingConversion(char* target_type, char* source_type) {
    int target_rank = getTypeRank(target_type);
    int source_rank = getTypeRank(source_type);
    
    if (target_rank > 0 && source_rank > 0) {
        return source_rank > target_rank;
    }
    return 0;
}

void checkType(struct Expr* op1, struct Expr* op2, char* opr1, char* opr2, char* type){
    char* base_op1 = getBaseType(op1->type);
    char* base_op2 = getBaseType(op2->type);

    /* Pointer operands in arithmetic are not supported — emit error and bail */
    char n1[100], n2[100];
    normalizeType(base_op1, n1);
    normalizeType(base_op2, n2);
    if (isPointerType(n1) || isPointerType(n2)) {
        e = 1;
        sprintf(err+strlen(err),
            "Line %d: Error: invalid operands to arithmetic operator (pointer type '%s' and '%s')\n",
            yylineno,
            isPointerType(n1) ? n1 : base_op1,
            isPointerType(n2) ? n2 : base_op2);
        strcpy(opr1, ""); strcpy(opr2, "");
        strcpy(type, "int");
        return;
    }

    if (strcmp(base_op1, base_op2) == 0){
        strcpy(type, base_op1);
        strcpy(opr1, "");
        strcpy(opr2, "");
        return;
    }
    char* promoted = promoteType(base_op1, base_op2);
    strcpy(type, promoted);
    if (strcmp(base_op1, promoted) != 0){
        char* t = genvar();
        strcpy(opr1, t);
        sprintf(imcode[code], "%d %s = (%s) %s\n", code, opr1, promoted, op1->str);
        code++;
    } else {
        strcpy(opr1, "");
    }
    if (strcmp(base_op2, promoted) != 0){
        char* t = genvar();
        strcpy(opr2, t);
        sprintf(imcode[code], "%d %s = (%s) %s\n", code, opr2, promoted, op2->str);
        code++;
    } else {
        strcpy(opr2, "");
    }
}

void checkTypeAssign(struct Expr* op1, struct Expr* op2, char* opr){
    // If types match exactly, no conversion needed
    if (strcmp(op1->type, op2->type) == 0){ 
        strcpy(opr, ""); 
        return; 
    }
    
    // Clean up const qualifiers
    char base_op1_type[100], base_op2_type[100];
    strcpy(base_op1_type, op1->type);
    strcpy(base_op2_type, op2->type);
    char* actual_op1 = base_op1_type;
    char* actual_op2 = base_op2_type;
    if (strncmp(base_op1_type, "const ", 6) == 0) actual_op1 = base_op1_type + 6;
    if (strncmp(base_op2_type, "const ", 6) == 0) actual_op2 = base_op2_type + 6;
    
    // Get base types (without array dimensions)
    char* op1_base = getBaseType(actual_op1);
    char* op2_base = getBaseType(actual_op2);
    
    // If base types match, no conversion needed
    if (strcmp(op1_base, op2_base) == 0) { 
        strcpy(opr, ""); 
        return; 
    }

    /* ── pointer type safety ──
       Normalise "char*" → "ptr:char" so string literals and ptr:char unify. */
    char n1[100], n2[100];
    normalizeType(op1_base, n1);
    normalizeType(op2_base, n2);
    int op1_is_ptr = isPointerType(n1);
    int op2_is_ptr = isPointerType(n2);
    if (op1_is_ptr || op2_is_ptr) {
        if (op1_is_ptr && !op2_is_ptr) {
            /* ptr:T ← non-ptr: only literal 0 (null) is allowed */
            if (!(strcmp(op2->str,"0")==0 || strcmp(op2->str,"0.0")==0)) {
                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: Type error: cannot assign non-pointer '%s' to pointer variable of type '%s'\n",
                    yylineno, op2_base, n1);
            }
        } else if (!op1_is_ptr && op2_is_ptr) {
            e = 1;
            sprintf(err+strlen(err),
                "Line %d: Type error: cannot assign pointer '%s' to non-pointer variable of type '%s'\n",
                yylineno, n2, op1_base);
        } else if (strcmp(n1, n2) != 0) {
            /* ptr:T ← ptr:U — warn but allow */
            sprintf(err+strlen(err),
                "Line %d: Warning: pointer type mismatch in assignment: assigning '%s' to '%s'\n",
                yylineno, n2, n1);
        }
        strcpy(opr, "");
        return;
    }

    // Check for narrowing conversion and issue warnings
    int rank1 = getTypeRank(op1_base);
    int rank2 = getTypeRank(op2_base);
    
    if (rank1 > 0 && rank2 > 0) {
        // Both are numeric types
        if (rank2 > rank1) {
            // Narrowing conversion
            sprintf(err+strlen(err), 
                "Warning: Implicit narrowing conversion from %s to %s may lose data\n",
                op2_base, op1_base);
        }
        
        // Special warning for float/double to integer conversion
        if (isFloatingType(op2_base) && isIntegerType(op1_base)) {
            sprintf(err+strlen(err), 
                "Warning: Conversion from %s to %s will discard fractional part\n",
                op2_base, op1_base);
        }
        
        // Check literal range if it's a constant value
        if (isLiteral(op2->str)) {
            checkLiteralRange(op2->str, op1_base);
        }
    }
    
    // Generate the conversion
    if (isLiteral(op2->str)) {
        // For literals, do compile-time cast
        sprintf(opr, "(%s)%s", op1_base, op2->str);
    } else {
        // For variables, generate cast instruction
        char* temp = genvar();
        sprintf(imcode[code], "%d %s = (%s) %s\n", code, temp, op1_base, op2->str);
        code++;
        strcpy(opr, temp);
    }
}


void identityAssignmentElimination() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        if (strstr(imcode[i], " ref ")   != NULL) continue;
        if (strstr(imcode[i], " deref ") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char lhs[100], rhs[100];
        if (sscanf(line, "%d %s = %[^\n]", &line_num, lhs, rhs) == 3) {
            char* end = rhs + strlen(rhs) - 1;
            while (end > rhs && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }
            if (strcmp(lhs, rhs) == 0)
                sprintf(imcode[i], "%d // IDENTITY: %s = %s (eliminated)\n", line_num, lhs, rhs);
        }
    }
}

void deadStoreElimination() {
    for (int i = 0; i < code - 1; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        /* Never touch "N deref p = val" store-through-pointer lines */
        {
            const char* alnp = line + strspn(line, "0123456789 ");
            if (strncmp(alnp, "deref ", 6) == 0) continue;
        }
        int line_num; char lhs[100], rhs[100];
        if (sscanf(line, "%d %s = %[^\n]", &line_num, lhs, rhs) == 3) {
            if (strstr(rhs, "Call") != NULL || strstr(rhs, "PopParam") != NULL) continue;
            /* Never eliminate ref/deref assignments — they have pointer side-effects */
            if (strstr(rhs, "ref ") != NULL || strstr(rhs, "deref ") != NULL) continue;
            /* Never eliminate heap allocation — each call produces a distinct block */
            if (strstr(rhs, "ALLOC") != NULL || strstr(rhs, "CALLOC") != NULL ||
                strstr(rhs, "REALLOC") != NULL) continue;
            for (int j = i + 1; j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                /* Stop at control flow boundaries */
                if (strstr(imcode[j], "if ") != NULL || strstr(imcode[j], "goto ") != NULL ||
                    strstr(imcode[j], "BeginFunc") != NULL ||
                    strstr(imcode[j], "EndFunc") != NULL) break;
                char check_line[10000]; strcpy(check_line, imcode[j]);
                char check_lhs[100];
                char* equals = strchr(check_line, '=');
                if (equals) {
                    /* Variable used on RHS of an assignment — not a dead store */
                    char* rhs_part = equals + 1;
                    if (strstr(rhs_part, lhs) != NULL) break;
                } else {
                    /* No '=' — this is a use-only instruction:
                       printint/printfloat/printchar/printstring,
                       PushParam, Return, inputint etc.
                       If lhs appears anywhere in the line it is being used. */
                    /* Build a word-boundary check to avoid false matches
                       e.g. lhs="x" matching inside "xy" */
                    char* p = check_line;
                    int lhs_len = strlen(lhs);
                    int used = 0;
                    while ((p = strstr(p, lhs)) != NULL) {
                        char before = (p == check_line) ? ' ' : *(p - 1);
                        char after  = *(p + lhs_len);
                        if (!isalnum((unsigned char)before) && before != '_' &&
                            !isalnum((unsigned char)after)  && after  != '_') {
                            used = 1; break;
                        }
                        p++;
                    }
                    if (used) break;
                }
                /* Variable overwritten before any use — dead store */
                if (sscanf(check_line, "%*d %s =", check_lhs) == 1) {
                    if (strcmp(check_lhs, lhs) == 0) {
                        /* Guard: find enclosing BeginFunc and check ref-param */
                        int enclosing_begin = -1;
                        for (int k = i - 1; k >= 0; k--) {
                            if (strstr(imcode[k], "BeginFunc") != NULL) {
                                enclosing_begin = k; break;
                            }
                        }
                        if (enclosing_begin >= 0 && is_ref_param(enclosing_begin, lhs))
                            break; /* not a dead store — ref-param write is externally visible */
                        sprintf(imcode[i], "%d // DEAD STORE: %s = %s\n", line_num, lhs, rhs);
                        break;
                    }
                }
            }
        }
    }
}



void redundantLoadElimination() {
    /* Build jump-target table: any line that is a goto destination is a
       join point. Replacing across a join point is unsafe because a path
       that bypasses the definition may reach the join with a stale value. */
    int is_jump_target[10000] = {0};
    for (int ii = 0; ii < code; ii++) {
        if (strstr(imcode[ii], "// DEAD") != NULL) continue;
        char *gp = strstr(imcode[ii], "goto");
        if (!gp) continue;
        char *tp = gp + 4; while (*tp == ' ' || *tp == '\t') tp++;
        if (isdigit((unsigned char)*tp)) {
            int tgt = atoi(tp);
            if (tgt >= 0 && tgt < code) is_jump_target[tgt] = 1;
        }
    }

    for (int i = 0; i < code - 1; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        if (strstr(imcode[i], " ref ")   != NULL) continue;
        if (strstr(imcode[i], " deref ") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char lhs[100], rhs[100];
        if (sscanf(line, "%d %s = %[^\n]", &line_num, lhs, rhs) == 3) {
            char* end = rhs + strlen(rhs) - 1;
            while (end > rhs && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }

            /* Skip complex expressions and non-variable RHS */
            if (strchr(rhs, '+') != NULL || strchr(rhs, '-') != NULL ||
                strchr(rhs, '*') != NULL || strchr(rhs, '/') != NULL ||
                strchr(rhs, '%') != NULL || strchr(rhs, '&') != NULL ||
                strchr(rhs, '|') != NULL || strchr(rhs, '^') != NULL ||
                strstr(rhs, "<<") != NULL || strstr(rhs, ">>") != NULL ||
                strstr(rhs, "Call") != NULL) continue;
            if (isNumericConstant(rhs) || isLiteral(rhs)) continue;

            int lhs_len = strlen(lhs);
            int rhs_len = strlen(rhs);

            /* Scan forward for a redundant load of the same rhs */
            for (int j = i + 1; j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;

                /* Stop at control-flow / function boundaries */
                if (strstr(imcode[j], "if ")      != NULL ||
                    strstr(imcode[j], "goto ")     != NULL ||
                    strstr(imcode[j], "Return")    != NULL ||
                    strstr(imcode[j], "BeginFunc") != NULL ||
                    strstr(imcode[j], "EndFunc")   != NULL) break;

                /* Stop at any pointer operation — a deref store may change memory
                   that rhs reads from, making earlier cached values stale */
                if (strstr(imcode[j], " ref ")   != NULL) break;
                if (strstr(imcode[j], " deref ") != NULL) break;
                {
                    const char* alnp_j = imcode[j] + strspn(imcode[j], "0123456789 ");
                    if (strncmp(alnp_j, "deref ", 6) == 0) break;
                }

                /* Stop at join points */
                if (is_jump_target[j]) break;

                char jline[10000]; strcpy(jline, imcode[j]);
                int j_line_num; char j_lhs[100], j_rhs[100];

                /* Word-boundary check: is lhs used on this line?
                   (prevents "a" matching inside "arr") */
                {
                    int used = 0;
                    char* p = jline;
                    while ((p = strstr(p, lhs)) != NULL) {
                        char before = (p == jline) ? ' ' : *(p - 1);
                        char after  = *(p + lhs_len);
                        if (!isalnum((unsigned char)before) && before != '_' &&
                            !isalnum((unsigned char)after)  && after  != '_') {
                            used = 1; break;
                        }
                        p++;
                    }
                    if (used) break;
                }

                /* If rhs (source) is overwritten here, stop — later loads differ */
                if (sscanf(jline, "%*d %s =", j_lhs) == 1) {
                    /* word-boundary check on rhs too (e.g. rhs="arr[8]", lhs="arr") */
                    if (strcmp(j_lhs, rhs) == 0) break;
                    /* also stop if LHS of this line IS rhs (handles array base names) */
                    if (strncmp(j_lhs, rhs, rhs_len) == 0 &&
                        (j_lhs[rhs_len] == '[' || j_lhs[rhs_len] == '\0')) break;
                }

                /* Found another load of the same rhs into a different variable */
                if (sscanf(jline, "%d %s = %[^\n]", &j_line_num, j_lhs, j_rhs) == 3) {
                    char* je = j_rhs + strlen(j_rhs) - 1;
                    while (je > j_rhs && (*je == ' ' || *je == '\n')) { *je = '\0'; je--; }
                    if (strcmp(j_rhs, rhs) == 0 && strcmp(j_lhs, lhs) != 0) {
                        sprintf(imcode[j], "%d %s = %s\n", j_line_num, j_lhs, lhs);
                    }
                }
            }
        }
    }
}

void peepholeOptimization() {
    for (int i = 0; i < code - 1; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        if (strstr(imcode[i],   " ref ")   != NULL) continue;
        if (strstr(imcode[i],   " deref ") != NULL) continue;
        if (strstr(imcode[i+1], " ref ")   != NULL) continue;
        if (strstr(imcode[i+1], " deref ") != NULL) continue;
        char line1[10000], line2[10000];
        strcpy(line1, imcode[i]); strcpy(line2, imcode[i+1]);
        int line_num1, line_num2; char lhs1[100], rhs1[100], lhs2[100], rhs2[100];
        if (sscanf(line1, "%d %s = %[^\n]", &line_num1, lhs1, rhs1) == 3 &&
            sscanf(line2, "%d %s = %[^\n]", &line_num2, lhs2, rhs2) == 3) {
            char* end = rhs1 + strlen(rhs1) - 1;
            while (end > rhs1 && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }
            end = rhs2 + strlen(rhs2) - 1;
            while (end > rhs2 && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }
            if (strchr(rhs1,'+') == NULL && strchr(rhs1,'-') == NULL &&
                strchr(rhs1,'*') == NULL && strchr(rhs1,'/') == NULL &&
                strchr(rhs2,'+') == NULL && strchr(rhs2,'-') == NULL &&
                strchr(rhs2,'*') == NULL && strchr(rhs2,'/') == NULL) {
                if (strcmp(lhs1, rhs2) == 0 && strcmp(rhs1, lhs2) == 0)
                    sprintf(imcode[i+1], "%d // PEEPHOLE: %s = %s (redundant swap)\n", line_num2, lhs2, rhs2);
            }
        }
    }
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        if (strstr(imcode[i], "// PEEPHOLE") != NULL) continue;
        /* Skip ref/deref lines — pointer semantics must not be collapsed */
        if (strstr(imcode[i], " ref ")   != NULL) continue;
        if (strstr(imcode[i], " deref ") != NULL) continue;
        {
            const char* alnp = imcode[i] + strspn(imcode[i], "0123456789 ");
            if (strncmp(alnp, "deref ", 6) == 0) continue;
        }
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char lhs[100], rhs[100];
        if (sscanf(line, "%d %s = %[^\n]", &line_num, lhs, rhs) == 3) {
            char* end = rhs + strlen(rhs) - 1;
            while (end > rhs && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }
            if (strchr(rhs,'+') != NULL || strchr(rhs,'-') != NULL ||
                strchr(rhs,'*') != NULL || strchr(rhs,'/') != NULL ||
                strchr(rhs,'(') != NULL) continue;
            for (int j = i + 1; j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                if (strstr(imcode[j], "// PEEPHOLE") != NULL) continue;
                if (strstr(imcode[j], " ref ")   != NULL) break;
                if (strstr(imcode[j], " deref ") != NULL) break;
                {
                    const char* alnp_j = imcode[j] + strspn(imcode[j], "0123456789 ");
                    if (strncmp(alnp_j, "deref ", 6) == 0) break;
                }
                char check_line[10000]; strcpy(check_line, imcode[j]);
                if (strstr(check_line, "BeginFunc") != NULL || strstr(check_line, "EndFunc") != NULL) break;
                if (strstr(check_line, "if ") != NULL || strstr(check_line, "goto ") != NULL ||
                    strstr(check_line, "Return") != NULL) break;
                char check_lhs[100], check_rhs[100];
                if (sscanf(check_line, "%*d %s = %[^\n]", check_lhs, check_rhs) == 2) {
                    char* check_end = check_rhs + strlen(check_rhs) - 1;
                    while (check_end > check_rhs && (*check_end == ' ' || *check_end == '\n')) { *check_end = '\0'; check_end--; }
                    if (strcmp(check_lhs, lhs) == 0) {
                        if (strcmp(check_rhs, rhs) == 0) {
                            int check_line_num; sscanf(imcode[j], "%d", &check_line_num);
                            sprintf(imcode[j], "%d // PEEPHOLE: %s = %s (redundant reassignment)\n", check_line_num, check_lhs, check_rhs);
                        }
                        break;
                    }
                    if (strcmp(check_lhs, rhs) == 0) break;
                }
            }
        }
    }
}

void strengthReduction() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1[100], op[10], op2[100];
        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1, op, op2) == 5) {
            if (!isNumericConstant(op2)) {
                if (!isNumericConstant(op1)) continue;
                char temp[100]; strcpy(temp, op1); strcpy(op1, op2); strcpy(op2, temp);
            }
            int constant = atoi(op2);
            if (strcmp(op, "*") == 0 && constant > 0) {
                if ((constant & (constant - 1)) == 0) {
                    int shift = 0; int temp = constant;
                    while (temp > 1) { temp >>= 1; shift++; }
                    if (constant == 2) sprintf(imcode[i], "%d %s = %s + %s\n", line_num, result, op1, op1);
                    else sprintf(imcode[i], "%d %s = %s << %d\n", line_num, result, op1, shift);
                    continue;
                }
            }
            if (strcmp(op, "/") == 0 && constant > 0) {
                if ((constant & (constant - 1)) == 0) {
                    int shift = 0; int temp = constant;
                    while (temp > 1) { temp >>= 1; shift++; }
                    sprintf(imcode[i], "%d %s = %s >> %d\n", line_num, result, op1, shift);
                    continue;
                }
            }
        }
    }
}

void algebraicSimplification() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1[100], op[10], op2[100];
        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1, op, op2) == 5) {

            /*  Multiplication  */
            if (strcmp(op,"*")==0 && strcmp(op2,"1")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"*")==0 && strcmp(op1,"1")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"*")==0 && strcmp(op2,"0")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"*")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }

            /*  Addition / Subtraction  */
            if ((strcmp(op,"+")==0||strcmp(op,"-")==0) && strcmp(op2,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"+")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"-")==0 && strcmp(op1,op2)==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }

            /*  Division  */
            if (strcmp(op,"/")==0 && strcmp(op2,"1")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"/")==0 && strcmp(op1,op2)==0){ sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            if (strcmp(op,"/")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }

            /*  Modulo  */
            if (strcmp(op,"%")==0 && strcmp(op2,"1")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  /* x % 1 == 0 */
            if (strcmp(op,"%")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  /* 0 % x == 0 */
            if (strcmp(op,"%")==0 && strcmp(op1,op2)==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  /* x % x == 0 */

            /*  Bitwise AND (bitand)  */
            if (strcmp(op,"&")==0 && (strcmp(op2,"0")==0||strcmp(op1,"0")==0)){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"&")==0 && strcmp(op1,op2)==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  /* x & x == x */

            /*  Bitwise OR (bitor)  */
            if (strcmp(op,"|")==0 && strcmp(op2,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"|")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"|")==0 && strcmp(op1,op2)==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  /* x | x == x */

            /*  Bitwise XOR (bitxor)  */
            if (strcmp(op,"^")==0 && strcmp(op2,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"^")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"^")==0 && strcmp(op1,op2)==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  /* x ^ x == 0 */

            /*  Left Shift (lshift → <<)  */
            if (strcmp(op,"<<")==0 && strcmp(op2,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  /* x << 0 == x */
            if (strcmp(op,"<<")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }        /* 0 << x == 0 */

            /*  Right Shift (rshift → >>)  */
            if (strcmp(op,">>")==0 && strcmp(op2,"0")==0){ sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  /* x >> 0 == x */
            if (strcmp(op,">>")==0 && strcmp(op1,"0")==0){ sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }        /* 0 >> x == 0 */
        }
    }
}

/*
void constantFoldConditionals() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        char line[10000];
        strcpy(line, imcode[i]);
        
        int line_num;
        char cond[1000];
        if (sscanf(line, "%d if %[^\n]", &line_num, cond) == 2) {
            char op1[100], op[10], op2[100], rest[100];
            if (sscanf(cond, "%s %s %s %[^\n]", op1, op, op2, rest) == 4) {
                if (isNumericConstant(op1) && isNumericConstant(op2)) {
                    double v1 = atof(op1), v2 = atof(op2);
                    int result = 0;
                    if (strcmp(op, "<") == 0) result = (v1 < v2);
                    else if (strcmp(op, ">") == 0) result = (v1 > v2);
                    else if (strcmp(op, "<=") == 0) result = (v1 <= v2);
                    else if (strcmp(op, ">=") == 0) result = (v1 >= v2);
                    else if (strcmp(op, "==") == 0) result = (v1 == v2);
                    else if (strcmp(op, "!=") == 0) result = (v1 != v2);
                    
                    if (result) {
                        char* goto_ptr = strstr(rest, "goto");
                        if (goto_ptr) {
                            sprintf(imcode[i], "%d %s\n", line_num, goto_ptr);
                        }
                    } else {
                        sprintf(imcode[i], "%d // DEAD BRANCH: if %s %s %s always false\n", 
                                line_num, op1, op, op2);
                    }
                }
            }
        }
    }
}
*/





void constantFoldConditionals() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        char line[10000];
        strcpy(line, imcode[i]);
        
        int line_num;
        char cond[1000];
        if (sscanf(line, "%d if %[^\n]", &line_num, cond) == 2) {
            char op1[100], op[10], op2[100], rest[100];
            if (sscanf(cond, "%s %s %s %[^\n]", op1, op, op2, rest) == 4) {
                // Try to resolve operands to their constant values
                char resolved_op1[100], resolved_op2[100];
                strcpy(resolved_op1, op1);
                strcpy(resolved_op2, op2);
                int op1_is_truly_constant = 1;
                int op2_is_truly_constant = 1;
                
                // Look up op1 if it's a variable
                if (!isNumericConstant(op1)) {
                    int assignment_count = 0;
                    for (int j = 0; j < code; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char check_line[10000]; strcpy(check_line, imcode[j]);
                        char lhs[100];
                        if (sscanf(check_line, "%*d %s = %*[^\n]", lhs) == 1) {
                            if (strcmp(lhs, op1) == 0) {
                                assignment_count++;
                                if (assignment_count > 1) {
                                    op1_is_truly_constant = 0;
                                    break;
                                }
                            }
                        }
                    }
                    
                    if (op1_is_truly_constant) {
                        for (int j = i - 1; j >= 0; j--) {
                            if (strstr(imcode[j], "// DEAD") != NULL) continue;
                            char check_line[10000]; strcpy(check_line, imcode[j]);
                            char lhs[100], rhs[100];
                            if (sscanf(check_line, "%*d %s = %[^\n]", lhs, rhs) == 2) {
                                if (strcmp(lhs, op1) == 0) {
                                    char* trimmed = rhs;
                                    while (*trimmed == ' ') trimmed++;
                                    char* end = trimmed + strlen(trimmed) - 1;
                                    while (end > trimmed && (*end == ' ' || *end == '\n')) end--;
                                    *(end + 1) = '\0';
                                    
                                    if (isNumericConstant(trimmed) && 
                                        !strchr(trimmed, '+') && !strchr(trimmed, '-') &&
                                        !strchr(trimmed, '*') && !strchr(trimmed, '/')) {
                                        strcpy(resolved_op1, trimmed);
                                    } else {
                                        op1_is_truly_constant = 0;
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
                
                // Look up op2 if it's a variable
                if (!isNumericConstant(op2)) {
                    int assignment_count = 0;
                    for (int j = 0; j < code; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char check_line[10000]; strcpy(check_line, imcode[j]);
                        char lhs[100];
                        if (sscanf(check_line, "%*d %s = %*[^\n]", lhs) == 1) {
                            if (strcmp(lhs, op2) == 0) {
                                assignment_count++;
                                if (assignment_count > 1) {
                                    op2_is_truly_constant = 0;
                                    break;
                                }
                            }
                        }
                    }
                    
                    if (op2_is_truly_constant) {
                        for (int j = i - 1; j >= 0; j--) {
                            if (strstr(imcode[j], "// DEAD") != NULL) continue;
                            char check_line[10000]; strcpy(check_line, imcode[j]);
                            char lhs[100], rhs[100];
                            if (sscanf(check_line, "%*d %s = %[^\n]", lhs, rhs) == 2) {
                                if (strcmp(lhs, op2) == 0) {
                                    char* trimmed = rhs;
                                    while (*trimmed == ' ') trimmed++;
                                    char* end = trimmed + strlen(trimmed) - 1;
                                    while (end > trimmed && (*end == ' ' || *end == '\n')) end--;
                                    *(end + 1) = '\0';
                                    
                                    if (isNumericConstant(trimmed) && 
                                        !strchr(trimmed, '+') && !strchr(trimmed, '-') &&
                                        !strchr(trimmed, '*') && !strchr(trimmed, '/')) {
                                        strcpy(resolved_op2, trimmed);
                                    } else {
                                        op2_is_truly_constant = 0;
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
                
                // Only fold if both are truly constant (assigned only once with constant values)
                if (op1_is_truly_constant && op2_is_truly_constant &&
                    isNumericConstant(resolved_op1) && isNumericConstant(resolved_op2)) {
                    double v1 = atof(resolved_op1), v2 = atof(resolved_op2);
                    int result = 0;
                    if (strcmp(op, "<") == 0) result = (v1 < v2);
                    else if (strcmp(op, ">") == 0) result = (v1 > v2);
                    else if (strcmp(op, "<=") == 0) result = (v1 <= v2);
                    else if (strcmp(op, ">=") == 0) result = (v1 >= v2);
                    else if (strcmp(op, "==") == 0) result = (v1 == v2);
                    else if (strcmp(op, "!=") == 0) result = (v1 != v2);
                    
                    if (result) {
                        char* goto_ptr = strstr(rest, "goto");
                        if (goto_ptr) {
                            sprintf(imcode[i], "%d %s // FOLDED: if %s %s %s always true\n", 
                                    line_num, goto_ptr, resolved_op1, op, resolved_op2);
                        }
                    } else {
                        sprintf(imcode[i], "%d // DEAD BRANCH: if %s %s %s always false\n", 
                                line_num, resolved_op1, op, resolved_op2);
                    }
                }
            }
        }
    }
}



static int is_ref_param(int func_start_idx, const char *varname) {
    char fname[256] = "";
    /* BeginFunc line format: "N BeginFunc funcname" */
    sscanf(imcode[func_start_idx], "%*d BeginFunc %255s", fname);
    if (!fname[0]) return 0;
    Function *f = findFunction(fname);
    if (!f) return 0;
    for (Param *p = f->params; p; p = p->next)
        if (strcmp(p->name , varname) == 0)
            return p->is_ref;   /* use dedicated flag; type[0]=='@' is unreliable after stripping */
    return 0;
}
void copyPropagation() {
    int is_jump_target[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "goto") != NULL) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) { int target = atoi(ptr); if (target >= 0 && target < code) is_jump_target[target] = 1; }
        }
    }
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char lhs[100], rhs[100];
        if (sscanf(line, "%d %s = %[^\n]", &line_num, lhs, rhs) == 3) {
            char* end = rhs + strlen(rhs) - 1;
            while (end > rhs && (*end == ' ' || *end == '\n' || *end == '\r')) { *end = '\0'; end--; }
            if (strchr(lhs, '[') != NULL) continue;
            /* Never propagate into or through pointer-operation lines */
            if (strstr(imcode[i], " ref ")   != NULL) continue;
            if (strstr(imcode[i], " deref ")  != NULL) continue;
            if (strncmp(imcode[i]+strspn(imcode[i],"0123456789 "), "deref ", 6) == 0) continue;
            if (strchr(rhs,'+')!=NULL||strchr(rhs,'-')!=NULL||strchr(rhs,'*')!=NULL||strchr(rhs,'/')!=NULL||
                strchr(rhs,'%')!=NULL||strchr(rhs,'&')!=NULL||strchr(rhs,'|')!=NULL||strchr(rhs,'^')!=NULL||
                strchr(rhs,'<')!=NULL||strchr(rhs,'>')!=NULL||strchr(rhs,'~')!=NULL||strchr(rhs,'(')!=NULL||
                strstr(rhs,"Call")!=NULL||strstr(rhs,"PopParam")!=NULL||strstr(rhs,"PushParam")!=NULL) continue;
            if (is_jump_target[i]) continue;
            int func_start = i, func_end = code;
            for (int k = i; k >= 0; k--) { if (strstr(imcode[k], "BeginFunc") != NULL) { func_start = k; break; } }
            for (int k = i; k < code; k++) { if (strstr(imcode[k], "EndFunc") != NULL) { func_end = k; break; } }
            int in_loop = 0;
            for (int j = func_start; j < func_end; j++) {
                if (strstr(imcode[j], "goto") != NULL) {
                    char* goto_ptr = strstr(imcode[j], "goto");
                    char* ptr = goto_ptr + 4;
                    while (*ptr == ' ' || *ptr == '\t') ptr++;
                    if (isdigit(*ptr)) { int target = atoi(ptr); if (target <= i && j >= i && i >= target && i <= j) { in_loop = 1; break; } }
                }
            }
            int first_modification = func_end;
            for (int j = i + 1; j < func_end; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                if (strstr(imcode[j], "EndFunc") != NULL) break;
                char check_lhs[100];
                if (sscanf(imcode[j], "%*d %s =", check_lhs) == 1) { if (strcmp(check_lhs, lhs) == 0) { first_modification = j; break; } }
            }
            int rhs_first_modification = func_end;
            if (!isNumericConstant(rhs)) {
                for (int j = i + 1; j < func_end; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    if (strstr(imcode[j], "EndFunc") != NULL) break;
                    char check_lhs[100];
                    if (sscanf(imcode[j], "%*d %s =", check_lhs) == 1) { if (strcmp(check_lhs, rhs) == 0) { rhs_first_modification = j; break; } }
                }
            }
            if (in_loop) continue;
            
            // Check if there's a goto between current line and first_modification
            int has_goto_before_modification = 0;
            int goto_target = -1;
            for (int j = i + 1; j < first_modification && j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                if (strstr(imcode[j], "goto") != NULL) {
                    char* goto_ptr = strstr(imcode[j], "goto");
                    char* ptr = goto_ptr + 4;
                    while (*ptr == ' ' || *ptr == '\t') ptr++;
                    if (isdigit(*ptr)) {
                        goto_target = atoi(ptr);
                        // If goto jumps past first_modification, we need to check beyond
                        if (goto_target > first_modification || goto_target > i + 1) {
                            has_goto_before_modification = 1;
                            break;
                        }
                    }
                }
            }
            
            // If there's a goto, extend safe_limit to check beyond the goto target
            int safe_limit = (first_modification < rhs_first_modification) ? first_modification : rhs_first_modification;
            if (has_goto_before_modification && goto_target > safe_limit) {
                // Only extend safe_limit if there are no further live assignments
                // to lhs between goto_target and func_end. If there are, the goto
                // skips over one assignment but another follows — we cannot safely
                // propagate the current value all the way to a use past that point.
                int has_later_assignment = 0;
                for (int j = goto_target; j < func_end; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    if (strstr(imcode[j], "EndFunc") != NULL) break;
                    char check_lhs2[100];
                    if (sscanf(imcode[j], "%*d %s =", check_lhs2) == 1) {
                        if (strcmp(check_lhs2, lhs) == 0) { has_later_assignment = 1; break; }
                    }
                }
                if (!has_later_assignment) {
                    // Safe to extend: goto skips intermediate assignment but no
                    // further writes exist, so the current value reaches the use.
                    safe_limit = (goto_target + 10 < func_end) ? goto_target + 10 : func_end;
                }
                // else: leave safe_limit at first_modification — don't propagate past it
            }
            
            int is_used = 0, last_use_line = -1;
            for (int j = i + 1; j < safe_limit && j < code; j++) {
                if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                char check_line[10000]; strcpy(check_line, imcode[j]);
                if (strstr(check_line, lhs) != NULL) {
                    char* pos = strstr(check_line, lhs);
                    while (pos) {
                        int is_whole = 1;
                        if (pos > check_line && (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\'')) is_whole = 0;
char after = *(pos + strlen(lhs));
if (isalnum(after) || after == '_' || after == '\'') is_whole = 0;

                        if (is_whole) { is_used = 1; last_use_line = j; }
                        pos = strstr(pos + 1, lhs);
                    }
                }
            }
            int is_constant = isLiteral(rhs); 
            if (is_used) {
               
                int use_inside_loop = 0;
                for (int j = func_start; j < func_end; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    if (strstr(imcode[j], "goto") != NULL) {
                        char* goto_ptr = strstr(imcode[j],"goto");
                        char* ptr = goto_ptr + 4;
                        while (*ptr == ' ' || *ptr == '\t') ptr++;
                        if (isdigit(*ptr)) {
                            int target = atoi(ptr);
                            /* backward branch whose target is at or before
                               last_use_line: use sites are inside a loop */
                            if (target <= last_use_line && j > target) {
                                use_inside_loop = 1;
                                break;
                            }
                        }
                    }
                }
                /* lhs is modified somewhere in the function after its definition
                   - its pre-loop value is stale on iteration 2+ - unsafe */
                if (use_inside_loop && first_modification < func_end) continue;

                int has_use_at_jump_target = 0;
                for (int j = i + 1; j <= last_use_line && j < code; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    if (is_jump_target[j]) {
                        char check_line[10000]; strcpy(check_line, imcode[j]);
                        if (strstr(check_line, lhs) != NULL) {
                            char* pos = strstr(check_line, lhs);
                            while (pos) {
                                int is_whole = 1;
                                if (pos > check_line && (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\'')) is_whole = 0;
char after = *(pos + strlen(lhs));
if (isalnum(after) || after == '_' || after == '\'') is_whole = 0;

                                if (is_whole) { has_use_at_jump_target = 1; break; }
                                pos = strstr(pos + 1, lhs);
                            }
                        }
                    }
                    if (has_use_at_jump_target) break;
                }
                if (has_use_at_jump_target) continue;
                int used_in_subscript = 0;
                for (int j = i + 1; j <= last_use_line && j < code; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    char check_line[10000]; strcpy(check_line, imcode[j]);
                    char* bracket_start = strchr(check_line, '[');
                    while (bracket_start) {
                        char* bracket_end = strchr(bracket_start, ']');
                        if (bracket_end) {
                            *bracket_end = '\0';
                            if (strstr(bracket_start, lhs) != NULL) { used_in_subscript = 1; *bracket_end = ']'; break; }
                            *bracket_end = ']';
                            bracket_start = strchr(bracket_end + 1, '[');
                        } else break;
                    }
                    if (used_in_subscript) break;
                }
                if (used_in_subscript && lhs[0] == 't' && isdigit(lhs[1]) && !is_constant) continue;
                int can_propagate = 0;
                if (lhs[0] == 't' && isdigit(lhs[1])) can_propagate = 1;
                else if (is_constant && !used_in_subscript) can_propagate = 1;
                if (!can_propagate) continue;
                /* Safety check for user variables (non-temps):
                   If any goto in the function can SKIP OVER line i
                   (goto source < i, goto target > i) then line i is inside
                   a conditional branch and may not execute — unsafe to propagate. */
                if (!(lhs[0] == 't' && isdigit(lhs[1]))) {
                    int inside_branch = 0;
                    for (int k = 0; k < func_end; k++) {
                        if (strstr(imcode[k], "// DEAD") != NULL) continue;
                        if (strstr(imcode[k], "goto") != NULL) {
                            char* goto_ptr = strstr(imcode[k], "goto");
                            char* ptr = goto_ptr + 4;
                            while (*ptr == ' ' || *ptr == '\t') ptr++;
                            if (isdigit(*ptr)) {
                                int gtarget = atoi(ptr);
                                /* A goto from before i that jumps past i means
                                   line i can be bypassed → it's in a branch */
                                if (k < i && gtarget > i) {
                                    inside_branch = 1;
                                    break;
                                }
                            }
                        }
                    }
                    if (inside_branch) continue;
                }
                for (int j = i + 1; j <= last_use_line && j < code && j < safe_limit; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    char new_line[10000]; strcpy(new_line, imcode[j]);
                    char* equals_sign = strchr(new_line, '=');
                    if (equals_sign == NULL) {
                        char* line_num_end = strchr(new_line, ' ');
                        char* search_start = line_num_end ? line_num_end + 1 : new_line;
                        char* pos = strstr(search_start, lhs);
                        while (pos != NULL) {
                            int is_whole_word = 1;
                             if (pos > search_start && (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\'')) is_whole_word = 0;
char after = *(pos + strlen(lhs));
if (isalnum(after) || after == '_' || after == '\'') is_whole_word = 0;
                            if (is_whole_word) {
                                char temp[10000]; *pos = '\0';
                                sprintf(temp, "%s%s%s", new_line, rhs, pos + strlen(lhs));
                                strcpy(new_line, temp); strcpy(imcode[j], new_line);
                                line_num_end = strchr(new_line, ' ');
                                search_start = line_num_end ? line_num_end + 1 : new_line;
                                pos = strstr(search_start, lhs);
                            } else pos = strstr(pos + 1, lhs);
                        }
                    } else {
                        char* line_num_end = strchr(new_line, ' ');
                        char* lhs_start = line_num_end ? line_num_end + 1 : new_line;
                        char* bracket_in_lhs = strchr(lhs_start, '[');
                        if (bracket_in_lhs && bracket_in_lhs < equals_sign) {
                            char* bracket_end = strchr(bracket_in_lhs, ']');
                            if (bracket_end && bracket_end < equals_sign) {
                                char* pos = strstr(bracket_in_lhs, lhs);
                                while (pos && pos < bracket_end) {
                                    int is_whole_word = 1;
                                    if (pos > bracket_in_lhs && (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\'')) is_whole_word = 0;
char after = *(pos + strlen(lhs));
if (isalnum(after) || after == '_' || after == '\'') is_whole_word = 0;
                                    if (is_whole_word) {
                                        char temp[10000]; *pos = '\0';
                                        sprintf(temp, "%s%s%s", new_line, rhs, pos + strlen(lhs));
                                        strcpy(new_line, temp); strcpy(imcode[j], new_line);
                                        equals_sign = strchr(new_line, '=');
                                        bracket_in_lhs = strchr(new_line, '[');
                                        bracket_end = strchr(bracket_in_lhs, ']');
                                        pos = strstr(bracket_in_lhs, lhs);
                                    } else { pos = strstr(pos + 1, lhs); if (pos >= bracket_end) break; }
                                }
                            }
                        }
                        char* rhs_start = equals_sign + 1;
                        char* pos = strstr(rhs_start, lhs);
                        while (pos != NULL) {
                            int is_whole_word = 1;
                            if (pos > rhs_start && (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\'')) is_whole_word = 0;
char after = *(pos + strlen(lhs));
if (isalnum(after) || after == '_' || after == '\'') is_whole_word = 0;

                            if (is_whole_word) {
                                char temp[10000]; *pos = '\0';
                                sprintf(temp, "%s%s%s", new_line, rhs, pos + strlen(lhs));
                                strcpy(new_line, temp); strcpy(imcode[j], new_line);
                                equals_sign = strchr(new_line, '=');
                                rhs_start = equals_sign + 1;
                                pos = strstr(rhs_start, lhs);
                            } else pos = strstr(pos + 1, lhs);
                        }
                    }
               /* }
                sprintf(imcode[i], "%d // DEAD COPY: %s = %s\n", line_num, lhs, rhs);
            }
            if (!is_used && is_constant) sprintf(imcode[i], "%d // DEAD CONST: %s = %s\n", line_num, lhs, rhs);
            */                }
                // Don't mark as DEAD COPY - keep the source definition
            } else if (!is_used && is_constant) {
                /* Before marking as DEAD CONST, do a full scan of the entire
                   function to make sure lhs is truly never READ anywhere after
                   this point. safe_limit may have cut the search short (stopped
                   at first_modification), missing a printint/return further down. */
                int globally_used = 0;
                for (int j = i + 1; j < func_end; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    char check_line[10000]; strcpy(check_line, imcode[j]);
                    /* Only count lhs as "used" when it appears on the READ side.
                       For an assignment "N lhs = ...", lhs on the LHS is a write,
                       not a read — skip those. We check reads by looking at:
                         - print/if/goto lines (no '=' before lhs)
                         - the RHS of assignment lines (after the '=')           */
                    char* eq = strchr(check_line, '=');
                    char* search_start;
                    if (eq == NULL) {
                        /* No '=' → whole line is a read context (printint, goto, if) */
                        search_start = check_line;
                    } else {
                        /* Has '=' → only scan the RHS (after '=') for reads */
                        search_start = eq + 1;
                    }
                    char* pos = strstr(search_start, lhs);
                    while (pos) {
                        int is_whole = 1;
                        if (pos > check_line &&
                            (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\''))
                            is_whole = 0;
                        char after2 = *(pos + strlen(lhs));
                        if (isalnum(after2) || after2 == '_' || after2 == '\'')
                            is_whole = 0;
                        if (is_whole) { globally_used = 1; break; }
                        pos = strstr(pos + 1, lhs);
                    }
                    if (globally_used) break;
                }
                if (!globally_used)
                    sprintf(imcode[i], "%d // DEAD CONST: %s = %s\n", line_num, lhs, rhs);
                /* else: keep the assignment live so the variable is initialised */
            }
        }      
    }
}



void booleanSimplification() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;

        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1[100], op[10], op2[100];

        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1, op, op2) == 5) {

            /* ── && (logical AND) ─────────────────────────────────────── */

            /* true && x  →  x */
            if (strcmp(op,"&&")==0 && strcmp(op1,"1")==0){
                sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            /* x && true  →  x */
            if (strcmp(op,"&&")==0 && strcmp(op2,"1")==0){
                sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            /* false && x  →  0 */
            if (strcmp(op,"&&")==0 && strcmp(op1,"0")==0){
                sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            /* x && false  →  0 */
            if (strcmp(op,"&&")==0 && strcmp(op2,"0")==0){
                sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            /* x && x  →  x */
            if (strcmp(op,"&&")==0 && strcmp(op1,op2)==0){
                sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }

            /* ── || (logical OR) ─────────────────────────────────────── */

            /* false || x  →  x */
            if (strcmp(op,"||")==0 && strcmp(op1,"0")==0){
                sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            /* x || false  →  x */
            if (strcmp(op,"||")==0 && strcmp(op2,"0")==0){
                sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            /* true || x  →  1 */
            if (strcmp(op,"||")==0 && strcmp(op1,"1")==0){
                sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            /* x || true  →  1 */
            if (strcmp(op,"||")==0 && strcmp(op2,"1")==0){
                sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            /* x || x  →  x */
            if (strcmp(op,"||")==0 && strcmp(op1,op2)==0){
                sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }

            /* ── == (equality) ───────────────────────────────────────── */

            /* x == x  →  1 */
            if (strcmp(op,"==")==0 && strcmp(op1,op2)==0){
                sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            /* two different numeric constants: fold at compile time */
            if (strcmp(op,"==")==0 && isNumericConstant(op1) && isNumericConstant(op2)){
                int r = (atof(op1) == atof(op2));
                sprintf(imcode[i],"%d %s = %d\n",line_num,result,r); continue; }

            /* ── != (not-equal) ──────────────────────────────────────── */

            /* x != x  →  0 */
            if (strcmp(op,"!=")==0 && strcmp(op1,op2)==0){
                sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            /* two different numeric constants: fold at compile time */
            if (strcmp(op,"!=")==0 && isNumericConstant(op1) && isNumericConstant(op2)){
                int r = (atof(op1) != atof(op2));
                sprintf(imcode[i],"%d %s = %d\n",line_num,result,r); continue; }
        }
    }
}




void conservativeJumpChaining() {
    // Pass 1: Count how many live gotos point to each line number.
    int ref_count[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char* p = imcode[i];
        char* gp;
        while ((gp = strstr(p, "goto")) != NULL) {
            char* tp = gp + 4;
            while (*tp == ' ' || *tp == '\t') tp++;
            if (isdigit(*tp)) {
                int t = atoi(tp);
                if (t >= 0 && t < code) ref_count[t]++;
            }
            p = gp + 1;
        }
    }

    // Pass 2: For each unconditional goto, follow the chain when safe.
    // We follow through line T only when:
    //   (a) T is a live, pure unconditional goto (no "if" before "goto"), AND
    //   (b) ref_count[T] == 1, meaning only the current jumper reaches T,
    //       so we can redirect past it without affecting other paths.
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;

        char line[10000];
        strcpy(line, imcode[i]);

        // Must be an unconditional goto: "N goto M"
        char* if_ptr   = strstr(line, "if");
        char* goto_ptr = strstr(line, "goto");
        if (!goto_ptr) continue;
        if (if_ptr && if_ptr < goto_ptr) continue;  // conditional — leave alone

        int line_num, target;
        if (sscanf(line, "%d goto %d", &line_num, &target) != 2) continue;

        int final_target = target;
        int steps = 0;

        while (steps++ < 1000) {
            if (final_target < 0 || final_target >= code) break;
            if (strstr(imcode[final_target], "// DEAD") != NULL) break;

            // Only safe to skip through if exactly one jumper reaches it
            if (ref_count[final_target] != 1) break;

            char mid[10000];
            strcpy(mid, imcode[final_target]);

            char* mid_if   = strstr(mid, "if");
            char* mid_goto = strstr(mid, "goto");
            if (!mid_goto) break;
            if (mid_if && mid_if < mid_goto) break;  // conditional

            int mid_num, next_target;
            if (sscanf(mid, "%d goto %d", &mid_num, &next_target) != 2) break;

            // Redirect: the intermediate line loses our reference, next gains it
            ref_count[final_target]--;
            ref_count[next_target]++;
            final_target = next_target;
        }

        if (final_target != target) {
            sprintf(imcode[i], "%d goto %d\n", line_num, final_target);
        }
    }
}


void constantFolding() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1_str[100], op[10], op2_str[100];
        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1_str, op, op2_str) == 5) {
            char resolved_op1[100], resolved_op2[100];
            strcpy(resolved_op1, op1_str); strcpy(resolved_op2, op2_str);
            int in_loop = 0;
            int func_start = i, func_end = code;
            for (int k = i; k >= 0; k--) { if (strstr(imcode[k], "BeginFunc") != NULL) { func_start = k; break; } }
            for (int k = i; k < code; k++) { if (strstr(imcode[k], "EndFunc") != NULL) { func_end = k; break; } }
            for (int k = func_start; k < func_end; k++) {
                if (strstr(imcode[k], "goto") != NULL) {
                    char* goto_ptr = strstr(imcode[k], "goto");
                    char* ptr = goto_ptr + 4;
                    while (*ptr == ' ' || *ptr == '\t') ptr++;
                    if (isdigit(*ptr)) { int target = atoi(ptr); if (target <= i && k >= i && i >= target && i <= k) { in_loop = 1; break; } }
                }
            }
            if (!isNumericConstant(op1_str)) {
                for (int j = i - 1; j >= 0; j--) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    if (strstr(imcode[j], "BeginFunc") != NULL) break;
                    char check_line[10000]; strcpy(check_line, imcode[j]);
                    char check_lhs[100], check_rhs[100];
                    if (sscanf(check_line, "%*d %s = %[^\n]", check_lhs, check_rhs) == 2) {
                        char* end = check_rhs + strlen(check_rhs) - 1;
                        while (end > check_rhs && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }
                        if (strcmp(check_lhs, op1_str) == 0) {
                            int is_modified = 0;
                            for (int k = j + 1; k < i; k++) {
                                if (strstr(imcode[k], "// DEAD") != NULL) continue;
                                char mod_check[100];
                                if (sscanf(imcode[k], "%*d %s =", mod_check) == 1) { if (strcmp(mod_check, op1_str) == 0) { is_modified = 1; break; } }
                            }
                            if (!is_modified && !in_loop && isNumericConstant(check_rhs) &&
                                strchr(check_rhs,'+')==NULL && strchr(check_rhs,'-')==NULL &&
                                strchr(check_rhs,'*')==NULL && strchr(check_rhs,'/')==NULL)
                                strcpy(resolved_op1, check_rhs);
                            break;
                        }
                    }
                }
            }
            if (!isNumericConstant(op2_str)) {
                for (int j = i - 1; j >= 0; j--) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    if (strstr(imcode[j], "BeginFunc") != NULL) break;
                    char check_line[10000]; strcpy(check_line, imcode[j]);
                    char check_lhs[100], check_rhs[100];
                    if (sscanf(check_line, "%*d %s = %[^\n]", check_lhs, check_rhs) == 2) {
                        char* end = check_rhs + strlen(check_rhs) - 1;
                        while (end > check_rhs && (*end == ' ' || *end == '\n')) { *end = '\0'; end--; }
                        if (strcmp(check_lhs, op2_str) == 0) {
                            int is_modified = 0;
                            for (int k = j + 1; k < i; k++) {
                                if (strstr(imcode[k], "// DEAD") != NULL) continue;
                                char mod_check[100];
                                if (sscanf(imcode[k], "%*d %s =", mod_check) == 1) { if (strcmp(mod_check, op2_str) == 0) { is_modified = 1; break; } }
                            }
                            if (!is_modified && !in_loop && isNumericConstant(check_rhs) &&
                                strchr(check_rhs,'+')==NULL && strchr(check_rhs,'-')==NULL &&
                                strchr(check_rhs,'*')==NULL && strchr(check_rhs,'/')==NULL)
                                strcpy(resolved_op2, check_rhs);
                            break;
                        }
                    }
                }
            }
            if (isNumericConstant(resolved_op1) && isNumericConstant(resolved_op2)) {
                double val1 = atof(resolved_op1), val2 = atof(resolved_op2), res = 0;
                int is_valid = 1;
                int is_float = (strchr(resolved_op1,'.')!=NULL || strchr(resolved_op2,'.')!=NULL);
                if (strcmp(op,"+")==0) res = val1+val2;
                else if (strcmp(op,"-")==0) res = val1-val2;
                else if (strcmp(op,"*")==0) res = val1*val2;
                else if (strcmp(op,"/")==0) { if (val2==0) is_valid=0; else { res=val1/val2;  } }
                else if (strcmp(op,"%")==0) { if (val2==0||is_float) is_valid=0; else res=(int)val1%(int)val2; }
                else if (strcmp(op,"&")==0) res=(int)val1&(int)val2;
                else if (strcmp(op,"|")==0) res=(int)val1|(int)val2;
                else if (strcmp(op,"^")==0) res=(int)val1^(int)val2;
                else if (strcmp(op,"<<")==0) res=(int)val1<<(int)val2;
                else if (strcmp(op,">>")==0) res=(int)val1>>(int)val2;
                else is_valid=0;
                if (is_valid) {
                    if (is_float) sprintf(imcode[i], "%d %s = %g\n", line_num, result, res);
                    else sprintf(imcode[i], "%d %s = %d\n", line_num, result, (int)res);
                }
            }
        }
    }
}

void deadVariableElimination() {
    int used[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        if (strstr(line,"print")!=NULL||strstr(line,"Return")!=NULL||strstr(line,"PushParam")!=NULL||
            strstr(line,"Call")!=NULL||strstr(line,"if")!=NULL||
            strstr(line,"FREE")!=NULL) {
            char* ptr = line;
            while (*ptr) {
                if (isalpha(*ptr) || *ptr == '_') {
                    char var[100]; int idx = 0;
                    while (isalnum(*ptr) || *ptr == '_') var[idx++] = *ptr++;
                    var[idx] = '\0';
                    if (strcmp(var,"if")==0||strcmp(var,"goto")==0||strcmp(var,"print")==0||
                        strcmp(var,"printint")==0||strcmp(var,"printfloat")==0||strcmp(var,"printchar")==0||
                        strcmp(var,"printstring")==0||strcmp(var,"Return")==0||strcmp(var,"Call")==0||
                        strcmp(var,"PushParam")==0||strcmp(var,"PopParam")==0||strcmp(var,"BeginFunc")==0||
                        strcmp(var,"EndFunc")==0||strcmp(var,"FREE")==0) continue;
                    for (int j = 0; j < code; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char check_line[10000]; strcpy(check_line, imcode[j]);
                        char lhs[100];
                        if (sscanf(check_line, "%*d %s =", lhs) == 1) { if (strcmp(lhs, var) == 0) used[j] = 1; }
                    }
                } else ptr++;
            }
        }
        char lhs_full[100];
        if (sscanf(line, "%*d %[^=]", lhs_full) == 1) {
            char* bracket_start = strchr(lhs_full, '[');
            if (bracket_start) {
                char* bracket_end = strchr(bracket_start, ']');
                if (bracket_end) {
                    char* ptr = bracket_start + 1;
                    while (ptr < bracket_end) {
                        if (isalpha(*ptr) || *ptr == '_') {
                            char var[100]; int idx = 0;
                            while ((isalnum(*ptr) || *ptr == '_') && ptr < bracket_end) var[idx++] = *ptr++;
                            var[idx] = '\0';
                            for (int j = 0; j < code; j++) {
                                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                                char check_line[10000]; strcpy(check_line, imcode[j]);
                                char check_lhs[100];
                                if (sscanf(check_line, "%*d %s =", check_lhs) == 1) { if (strcmp(check_lhs, var) == 0) used[j] = 1; }
                            }
                        } else ptr++;
                    }
                }
            }
        }
        char lhs[100];
        if (sscanf(line, "%*d %s =", lhs) == 1) {
            char* equals = strchr(line, '=');
            if (equals) {
                char* rhs = equals + 1;
                char* ptr = rhs;
                while (*ptr) {
                    if (isalpha(*ptr) || *ptr == '_') {
                        char var[100]; int idx = 0;
                        while (isalnum(*ptr) || *ptr == '_') var[idx++] = *ptr++;
                        var[idx] = '\0';
                        if (strcmp(var,"Call")==0||strcmp(var,"PopParam")==0||strcmp(var,"int")==0||
                            strcmp(var,"float")==0||strcmp(var,"char")==0||strcmp(var,"double")==0||
                            strcmp(var,"long")==0||strcmp(var,"short")==0||
                            strcmp(var,"ref")==0||strcmp(var,"deref")==0||
                            strcmp(var,"ALLOC")==0||strcmp(var,"CALLOC")==0||
                            strcmp(var,"REALLOC")==0||strcmp(var,"FREE")==0) continue;
                        for (int j = 0; j < code; j++) {
                            if (strstr(imcode[j], "// DEAD") != NULL) continue;
                            char check_line[10000]; strcpy(check_line, imcode[j]);
                            char check_lhs[100];
                            if (sscanf(check_line, "%*d %s =", check_lhs) == 1) { if (strcmp(check_lhs, var) == 0) used[j] = 1; }
                        }
                    } else ptr++;
                }
            }
        }
    }
    for (int i = 0; i < code; i++) {
        if (used[i] == 0 && strstr(imcode[i], "// DEAD") == NULL) {
            char line[10000]; strcpy(line, imcode[i]);
            char lhs[100];
            if (sscanf(line, "%*d %s =", lhs) == 1) {
                if (strstr(line,"BeginFunc")!=NULL||strstr(line,"EndFunc")!=NULL||
                    strstr(line,"PopParam")!=NULL||strstr(line,"Call")!=NULL) continue;
                /* Never eliminate pointer operations — they have memory side-effects */
                if (strstr(line," ref ") != NULL || strstr(line," deref ") != NULL) continue;
                /* Never eliminate heap allocation temporaries — side-effecting */
                if (strstr(line," ALLOC ") != NULL || strstr(line," CALLOC ") != NULL ||
                    strstr(line," REALLOC ") != NULL) continue;
                {
                    const char* alnp2 = line + strspn(line, "0123456789 ");
                    if (strncmp(alnp2, "deref ", 6) == 0) continue;
                }
                if (lhs[0] == 't' && isdigit(lhs[1])) {
                    char* content2 = strchr(line, ' ');
                    if (content2) { content2++; sprintf(imcode[i], "%d // DEAD VAR: %s", i, content2); }
                }
            }
        }
    }
}



void eliminateDeadCode() {
    // BUILD JUMP TARGET TABLE FIRST (moved to top) 
    int is_jump_target[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        if (strstr(imcode[i], "goto") != NULL) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) { int target = atoi(ptr); if (target >= 0 && target < code) is_jump_target[target] = 1; }
        }
    }
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        int is_unconditional = 0;
        if (strstr(imcode[i], "Return") != NULL) is_unconditional = 1;
        else if (strstr(imcode[i], "goto") != NULL) {
            char* if_ptr = strstr(imcode[i], "if");
            char* goto_ptr = strstr(imcode[i], "goto");
            if (goto_ptr && (!if_ptr || if_ptr > goto_ptr)) is_unconditional = 1;
        }
        if (is_unconditional) {
            int j = i + 1;
            if (j < code && strstr(imcode[j],"BeginFunc")==NULL && strstr(imcode[j],"EndFunc")==NULL &&
                strstr(imcode[j],"// DEAD CODE:")==NULL) {
                int is_live_target = is_jump_target[j];  // USE PREBUILT TABLE 
                if (!is_live_target) {
                    char original[10000]; strcpy(original, imcode[j]);
                    char* space_ptr = strchr(original, ' ');
                    if (space_ptr != NULL) { space_ptr++; sprintf(imcode[j], "%d // DEAD CODE: %s", j, space_ptr); }
                }
            }
        }
    }
    for (int i = 0; i < code; i++) {
        char* line = imcode[i];
        if (strstr(line, "// DEAD CODE:") != NULL) continue;
        int is_unconditional_jump = 0;
        if (strstr(line, "goto") != NULL) {
            char* if_ptr = strstr(line, "if");
            char* goto_ptr = strstr(line, "goto");
            if (goto_ptr && (!if_ptr || if_ptr > goto_ptr)) is_unconditional_jump = 1;
        } else if (strstr(line, "Return") != NULL) is_unconditional_jump = 1;
        if (is_unconditional_jump) {
            int j = i + 1;
            while (j < code) {
                if (strstr(imcode[j],"BeginFunc")!=NULL||strstr(imcode[j],"EndFunc")!=NULL) break;
                if (is_jump_target[j]) break;
                if (strstr(imcode[j],"// DEAD CODE:")!=NULL) { j++; continue; }
                char original[10000]; strcpy(original, imcode[j]);
                char* space_ptr = strchr(original, ' ');
                if (space_ptr != NULL) { space_ptr++; sprintf(imcode[j], "%d // DEAD CODE: %s", j, space_ptr); }
                j++;
            }
        }
    }
    int has_live_pred[10000] = {0};
    for (int i = 0; i < code; i++) { if (strstr(imcode[i],"BeginFunc")!=NULL && i+1<code) has_live_pred[i+1]=1; }
    has_live_pred[0] = 1;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i],"// DEAD CODE:")!=NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        if (strstr(line,"goto")!=NULL) {
            char* goto_ptr = strstr(line,"goto");
            char* ptr = goto_ptr+4;
            while (*ptr==' '||*ptr=='\t') ptr++;
            if (isdigit(*ptr)) { int target=atoi(ptr); if (target>=0&&target<code) has_live_pred[target]=1; }
        }
        int is_uncond = 0;
        if (strstr(line,"Return")!=NULL) is_uncond=1;
        else if (strstr(line,"goto")!=NULL) {
            char* if_ptr=strstr(line,"if"); char* goto_ptr=strstr(line,"goto");
            if (goto_ptr&&(!if_ptr||if_ptr>goto_ptr)) is_uncond=1;
        }
        if (!is_uncond && i+1<code) has_live_pred[i+1]=1;
    }
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i],"// DEAD CODE:")!=NULL) continue;
        if (strstr(imcode[i],"BeginFunc")!=NULL||strstr(imcode[i],"EndFunc")!=NULL) continue;
        if (!has_live_pred[i]) {
            char original[10000]; strcpy(original, imcode[i]);
            char* space_ptr = strchr(original, ' ');
            if (space_ptr!=NULL) { space_ptr++; sprintf(imcode[i], "%d // DEAD CODE: %s", i, space_ptr); }
        }
    }
}


void commonSubexpressionElimination() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        /* Heap allocation calls produce distinct blocks — never CSE them */
        if (strstr(line," ALLOC ")!=NULL||strstr(line," CALLOC ")!=NULL||
            strstr(line," REALLOC ")!=NULL) continue;
        int line_num; char result[100], op1[100], op[10], op2[100];
        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1, op, op2) == 5) {
            int func_start = i, func_end = code;
            for (int k = i; k >= 0; k--) { if (strstr(imcode[k],"BeginFunc")!=NULL) { func_start=k; break; } }
            for (int k = i; k < code; k++) { if (strstr(imcode[k],"EndFunc")!=NULL) { func_end=k; break; } }
            int loop_start = -1, loop_end = -1, min_loop_size = func_end;
            for (int k = i; k < func_end; k++) {
                if (strstr(imcode[k],"goto")!=NULL) {
                    char* goto_ptr=strstr(imcode[k],"goto");
                    char* if_ptr=strstr(imcode[k],"if");
                    if (if_ptr && if_ptr < goto_ptr) continue;
                    char* ptr = goto_ptr+4;
                    while (*ptr==' '||*ptr=='\t') ptr++;
                    if (isdigit(*ptr)) {
                        int target=atoi(ptr);
                        if (target<=i && k>=i) { int sz=k-target; if (sz<min_loop_size) { loop_start=target; loop_end=k; min_loop_size=sz; } }
                    }
                }
            }
            int search_start = i+1, search_end = (loop_start!=-1) ? loop_end : func_end;
            char resolved_op1[100], resolved_op2[100];
            strcpy(resolved_op1, op1); strcpy(resolved_op2, op2);
            for (int k = i-1; k >= func_start; k--) {
                if (strstr(imcode[k],"// DEAD")!=NULL) continue;
                if (strstr(imcode[k],"BeginFunc")!=NULL) break;
                char check_lhs[100], check_rhs[100];
                if (sscanf(imcode[k], "%*d %s = %[^\n]", check_lhs, check_rhs) == 2) {
                    char* end = check_rhs+strlen(check_rhs)-1;
                    while (end>check_rhs && (*end==' '||*end=='\n')) { *end='\0'; end--; }
                    if (strchr(check_rhs,'+')==NULL&&strchr(check_rhs,'-')==NULL&&strchr(check_rhs,'*')==NULL&&strchr(check_rhs,'/')==NULL&&strchr(check_rhs,'(')==NULL) {
                        if (strcmp(check_lhs,op1)==0) strcpy(resolved_op1, check_rhs);
                        if (strcmp(check_lhs,op2)==0) strcpy(resolved_op2, check_rhs);
                    }
                    if (strcmp(resolved_op1,op1)!=0 && strcmp(resolved_op2,op2)!=0) break;
                }
            }
            for (int j = search_start; j < search_end; j++) {
                if (strstr(imcode[j],"// DEAD CODE:")!=NULL) continue;
                char check_line[10000]; strcpy(check_line, imcode[j]);
                if (strstr(check_line,"if ")!=NULL||strstr(check_line,"goto ")!=NULL||strstr(check_line,"Return")!=NULL||
                    strstr(check_line,"BeginFunc")!=NULL||strstr(check_line,"EndFunc")!=NULL||
                    strstr(check_line,"PopParam")!=NULL||strstr(check_line,"PushParam")!=NULL||strstr(check_line,"Call")!=NULL||
                    strstr(check_line," ALLOC ")!=NULL||strstr(check_line," CALLOC ")!=NULL||
                    strstr(check_line," REALLOC ")!=NULL) continue;
                char redefined_var[100];
                if (sscanf(check_line, "%*d %s =", redefined_var) == 1) {
                    if (strcmp(redefined_var,resolved_op1)==0||strcmp(redefined_var,resolved_op2)==0) break;
                }
                int check_line_num; char check_result[100], check_op1[100], check_op[10], check_op2[100];
                if (sscanf(check_line, "%d %s = %s %s %s", &check_line_num, check_result, check_op1, check_op, check_op2) == 5) {
                    char resolved_check_op1[100], resolved_check_op2[100];
                    strcpy(resolved_check_op1, check_op1); strcpy(resolved_check_op2, check_op2);
                    for (int k = j-1; k >= func_start; k--) {
                        if (strstr(imcode[k],"// DEAD")!=NULL) continue;
                        if (strstr(imcode[k],"BeginFunc")!=NULL) break;
                        char k_lhs[100], k_rhs[100];
                        if (sscanf(imcode[k], "%*d %s = %[^\n]", k_lhs, k_rhs) == 2) {
                            char* end = k_rhs+strlen(k_rhs)-1;
                            while (end>k_rhs && (*end==' '||*end=='\n')) { *end='\0'; end--; }
                            if (strchr(k_rhs,'+')==NULL&&strchr(k_rhs,'-')==NULL&&strchr(k_rhs,'*')==NULL&&strchr(k_rhs,'/')==NULL&&strchr(k_rhs,'(')==NULL) {
                                if (strcmp(k_lhs,check_op1)==0) strcpy(resolved_check_op1, k_rhs);
                                if (strcmp(k_lhs,check_op2)==0) strcpy(resolved_check_op2, k_rhs);
                            }
                            if (strcmp(resolved_check_op1,check_op1)!=0 && strcmp(resolved_check_op2,check_op2)!=0) break;
                        }
                    }
                    if (strcmp(op,check_op)==0 && strcmp(resolved_op1,resolved_check_op1)==0 && strcmp(resolved_op2,resolved_check_op2)==0)
                        sprintf(imcode[j], "%d %s = %s\n", check_line_num, check_result, result);
                }
            }
        }
    }
}

%}

%union{
        char str[1000];
        struct BoolNode* b;
        struct Expr *expr;
        int addr;
        struct Type* type;
        struct Decl* decl;
        struct Subscript* sub;
}
%nonassoc error
%nonassoc PASN MASN DASN SASN
%right '?' ':'
%left OR
%left AND
%nonassoc '!'
%left LT GT LE GE EQ NE
%left BOR
%left BXOR
%left BAND
%left '+' '-'
%left '/' '*' '%'
%left LSHIFT RSHIFT
%nonassoc BNOT
%nonassoc INC DEC
%nonassoc '(' ')'
%nonassoc UMINUS ELSE IDEN
%nonassoc '$'
%token <str>ENUM  ABS MIN MAX MODASN BREAK CONTINUE FOR DO IDEN NUM PASN MASN DASN SASN INC DEC LT GT LE GE NE OR AND EQ IF ELSE TR FL WHILE INT FLOAT CHAR CHARR
%token MEOF
%token <str> CONST
%token SWITCH CASE DEFAULT
%type <str> ASSGN UN OPR
%token <str> GOTO
%token <str> STRING BOOL
%type <expr>  EXPR TERM
%type <b> BOOLEXPR STMNTS A ASNEXPR NN 
%type <addr> M
%type <type> TYPE INDEX
%type <decl> DECLLIST
%type <sub> SUBSCRIPTS
%token <str> PRINT INPUT
%token <str> SIZEOF 
%token BANDASN BORASN BXORASN LSHIFTASN RSHIFTASN
%token <str> SHORT LONG DOUBLE VOID
%token <str> PTRTYPE ADDROF DEREF
%token <str> BAND BOR BXOR BNOT LSHIFT RSHIFT
%token <str> FUNCTION RETURN CALL
/* ── Heap allocation tokens ── */
%token <str> ALLOC CALLOC REALLOC HFREE NULLPTR
%type <expr> INIT_LIST
%type <decl> PARAMLIST
%type <expr> ARGLIST FUNCALL
%type <b> PROGRAM FUNDECL
%type <b>  CASE_LIST CASE_ITEM
%type <expr> CASE_EXPR
%type <b> ENUM_MEMBER_LIST ENUM_MEMBER
%%


S:      {top = create_env(top,0);} PROGRAM M MEOF{
        if (e){
                        /*printf("%s\nRejected \n%s \nCould not generate Three Address Code / Storage Layout\n",buffer,err);*/
                        err[0]='\0';buffer[0]='\0';}
                else {
                        backpatch($2->N,$3);
                        //printf("%s\nAccepted -Unoptimized > Three Address :\n",buffer);
                     
                        /*for (int i=0;i<code;i++){
                                printf("%s",imcode[i]);
                        }*/
                          /*if (strlen(err) > 0) {
        printf("\n=== Warnings ===\n%s", err);
    }
                        print_all_envs(top);*/
         printQuadruples();
                }YYACCEPT;}
        | MEOF{YYACCEPT;}
        | error MEOF{e=1;strcpy(err,"Invalid Statements");
                //printf("%s \nRejected -> %s \nCould not generate Three Address Code / Storage Layout\n",buffer,err);
                YYACCEPT;};



PROGRAM: FUNDECL PROGRAM {
            if(!e){
                $$ = createBoolNode();
                $$->N = merge($1->N, $2->N);
            }
        }
        | A PROGRAM {
            if(!e){
                $$ = createBoolNode();
                $$->N = merge($1->N, $2->N);
            }
        }
        | FUNDECL {
            if(!e){
                $$ = createBoolNode();
                $$->N = $1->N;
            }
        }
        | A {$$ = $1;};


/* 
   FUNDECL  –   with: duplicate param check, loop/switch depth reset,
               function context tracking, non-void return warning
    */
FUNDECL: FUNCTION TYPE IDEN '(' PARAMLIST ')' {
    if(!e){
        /*  duplicate parameter check */
        if(checkDuplicateParams($5)){
            e = 1;
            sprintf(err+strlen(err), "Duplicate parameter names in function %s\n", $3);
        }

       // Function* f = createFunction($3, $2->str);
       char clean_ret_type[100];
strcpy(clean_ret_type, $2->str);
if(clean_ret_type[0] == '@') memmove(clean_ret_type, clean_ret_type+1, strlen(clean_ret_type));
Function* f = createFunction($3, clean_ret_type);  // stores "void", "int", "float" etc.
        f->start_label = code;

        struct Decl* p = $5;
        int pcount = 0;
        Param* param_tail = NULL;
        while(p){
            /* Strip leading '@' from param type before storing in Function struct */
            char clean_p_type[100];
            strcpy(clean_p_type, p->type);
            int param_is_ref = (clean_p_type[0] == '@');  /* capture BEFORE stripping */
            if (clean_p_type[0] == '@') memmove(clean_p_type, clean_p_type+1, strlen(clean_p_type));
            Param* param = createParam(p->key, clean_p_type);
            param->is_ref = param_is_ref;  /* ref status preserved independently of type string */
            pcount++;
            if(f->params == NULL){ f->params = param; param_tail = param; }
            else { param_tail->next = param; param_tail = param; }
            p = p->next;
        }
        f->param_count = pcount;

        if(findFunction($3) != NULL){
            e=1;
            sprintf(err+strlen(err),"Redeclaration of function %s\n",$3);
        } else {
            addFunction(f);
        }

        sprintf(imcode[code], "%d BeginFunc %s %d\n", code, $3, pcount);
        code++;

        /*  set current function context for return checking */
        char* ret_type_clean = $2->str;
        if(ret_type_clean[0]=='@') ret_type_clean++;
        strcpy(current_function, $3);
        strcpy(current_return_type, ret_type_clean);
        in_function = 1;
        has_return_statement = 0;

        top = create_env(top, offset);
        offset = 0;

        p = $5;
        while(p){
            Symbol* s = createSymbol(p->key);
            char clean_param_type[100];
            strcpy(clean_param_type, p->type);
            if (clean_param_type[0] == '@') memmove(clean_param_type, clean_param_type+1, strlen(clean_param_type));
            strcpy(s->type, clean_param_type);
            s->offset = offset;
            if(strcmp(clean_param_type,"char")==0) offset+=1;
            else if(strcmp(clean_param_type,"short")==0) offset+=2;
            else if(strcmp(clean_param_type,"int")==0||strcmp(clean_param_type,"float")==0) offset+=4;
            else if(strcmp(clean_param_type,"long")==0||strcmp(clean_param_type,"double")==0) offset+=8;
            else if(strncmp(clean_param_type,"ptr:",4)==0) offset+=8; /* pointer = 8 bytes on 64-bit */
            else offset+=4; /* default */
            put(top->table, p->key, s);
            sprintf(imcode[code], "%d PopParam %s\n", code, p->key);
            code++;
            p = p->next;
        }
    }
} '{' STMNTS '}' {
    if(!e){
    if(strcmp(current_return_type, "void") != 0 && !has_return_statement) {
    e = 1;
    sprintf(err + strlen(err), "Error: Non-void function '%s' must return a value of type %s\n", 
            current_function, current_return_type);
}

        sprintf(imcode[code], "%d EndFunc %s\n", code, $3);
        code++;

        $$ = createBoolNode();
        $$->N = $9->N;

        top = top->prev;
        if(!top) offset = 0;
        else offset = top->prev_offset;

        /*  reset function context */
        in_function = 0;
        current_function[0] = '\0';
        current_return_type[0] = '\0';
    }
};

PARAMLIST: TYPE IDEN ',' PARAMLIST {
            if(!e){
                $$ = createDecl($2);
                char clean_type[100];
                strcpy(clean_type, $1->str);
                if (clean_type[0] == '@') memmove(clean_type, clean_type+1, strlen(clean_type));
                strcpy($$->type, clean_type);
                $$->next = $4;
            }
        }
        | TYPE IDEN {
            if(!e){
                $$ = createDecl($2);
                char clean_type[100];
                strcpy(clean_type, $1->str);
                if (clean_type[0] == '@') memmove(clean_type, clean_type+1, strlen(clean_type));
                strcpy($$->type, clean_type);
            }
        }
        | {$$ = NULL;};


A:  SWITCH '(' EXPR ')' '{' { 
       if(!e) {
           strcpy(current_switch_var, $3->str);
           //saveoffset = offset;
                   top = create_env(top, offset);  
                  offset = 0;
                         char* base = getBaseType($3->type);
if(strstr($3->type, "[") != NULL) {
    // it's an array — always reject
    e = 1;
    sprintf(err+strlen(err),
        "Error: switch expression cannot be an array type '%s'\n", $3->type);
} else if(!isIntegerType(base)) {
    e = 1;
    sprintf(err+strlen(err),
        "Error: switch expression must be integer type, got '%s'\n", base);
}

           /*"" track switch depth "" */
           switch_depth++;
       }
   } CASE_LIST '}' {
       if(!e) {
           $$ = createBoolNode();
           backpatch($7->N, code);
           backpatch($7->B, code);
           //offset = saveoffset;
                   top = top->prev;            //  restore scope
        offset = top->prev_offset;  //  restore offset
           /*   restore switch depth  */
           switch_depth--;
       }
   }
| BREAK '$' {
    if (!e) {
        /*  break must be inside loop or switch */
        if(loop_depth == 0 && switch_depth == 0){
            e = 1;
            sprintf(err+strlen(err), "break statement not within loop or switch\n");
        }
        $$ = createBoolNode();
        $$->B = createNode(code);
        sprintf(imcode[code], "%d goto ", code);
        code++;
    }
}
| CONTINUE '$' {
    if (!e) {
        /*  continue must be inside a loop */
        if(loop_depth == 0){
            e = 1;
            sprintf(err+strlen(err), "continue statement not within a loop\n");
        }
        $$ = createBoolNode();
        $$->C = createNode(code);
        sprintf(imcode[code], "%d goto ", code);
        code++;
    }
}
| HFREE '(' EXPR ')' '$' {
    if(!e){
        if(!isPointerType($3->type) &&
           strcmp($3->str,"0") != 0) {
            e = 1;
            sprintf(err+strlen(err),
                "Line %d: Error: release() argument '%s' is not a pointer type (got '%s')\n",
                yylineno, $3->str, $3->type);
        } else {
            sprintf(imcode[code], "%d FREE %s\n", code, $3->str);
            code++;
        }
        $$ = createBoolNode();
    }
}
| RETURN EXPR '$' {
    if(!e){
        has_return_statement = 1;
        /*  return checks */
        if(!in_function){
            e = 1;
            sprintf(err+strlen(err), "return statement outside function\n");
        } else if(strcmp(current_return_type,"void")==0){
            e = 1;
            sprintf(err+strlen(err), "void function '%s' should not return a value\n", current_function);
        } else if(!isTypeCompatible(current_return_type, $2->type)){
            e = 1;
            sprintf(err+strlen(err), "Return type mismatch in function '%s': expected %s, got %s\n",
                    current_function, current_return_type, $2->type);
        }
         char ret_val[200];
        strcpy(ret_val, $2->str);
        char* ret_base = getBaseType(current_return_type);
        char* expr_base = getBaseType($2->type);
        if (!e && strlen(ret_base) > 0 && strcmp(ret_base, expr_base) != 0
               && getTypeRank(ret_base) > 0 && getTypeRank(expr_base) > 0) {
            /* generate:  t = (target_type) expr  then  Return t  */
            char* tmp = genvar();
            sprintf(imcode[code], "%d %s = (%s) %s\n", code, tmp, ret_base, $2->str);
            code++;
            strcpy(ret_val, tmp);
        }
                        sprintf(imcode[code], "%d Return %s\n", code, ret_val);
        code++;
        $$ = createBoolNode();
    }
}
| RETURN '$' {
    if(!e){
        has_return_statement = 1;
        /*  return checks */
        if(!in_function){
            e = 1;
            sprintf(err+strlen(err), "return statement outside function\n");
        } else if(strcmp(current_return_type, "void") != 0) {
    e = 1;
    sprintf(err + strlen(err), "Non-void function '%s' must return a value\n", current_function);
}

        sprintf(imcode[code], "%d Return\n", code);
        code++;
        $$ = createBoolNode();
    }
}

| CALL IDEN '(' ARGLIST ')' '$' {
    if(!e){
        Function* f = findFunction($2);
        if(f == NULL){
            e=1;
            sprintf(err+strlen(err), "Function %s not declared\n", $2);
        } else {
            struct Expr* arg = $4;
            int given = 0;
            while(arg){ given++; arg = arg->next; }
            if(given != f->param_count){
                e=1;
                sprintf(err+strlen(err),
                    "Function %s expects %d arguments, got %d\n",
                    $2, f->param_count, given);
            } else {
                arg = $4;
                Param* param = f->params;
                int arg_idx = 1;
                while(arg && param){
                    char* arg_base   = getBaseType(arg->type);
                    char* param_base = getBaseType(param->type);
                    char push_str[200];
                    strcpy(push_str, arg->str);
                    /* If types differ, insert an implicit cast (same rules as assignment) */
                    if(strcmp(arg_base, param_base) != 0 &&
                       getTypeRank(arg_base) > 0 && getTypeRank(param_base) > 0){
                        /* Warn on narrowing */
                        if(getTypeRank(arg_base) > getTypeRank(param_base)){
                            sprintf(err+strlen(err),
                                "Warning: Narrowing conversion from %s to %s for argument %d in call to '%s'\n",
                                arg_base, param_base, arg_idx, $2);
                        }
                        if(isFloatingType(arg_base) && isIntegerType(param_base)){
                            sprintf(err+strlen(err),
                                "Warning: Conversion from %s to %s for argument %d in call to '%s' will discard fractional part\n",
                                arg_base, param_base, arg_idx, $2);
                        }
                        if(isLiteral(arg->str)){
                            /* compile-time: inline the cast value */
                            sprintf(push_str, "(%s)%s", param_base, arg->str);
                        } else {
                            /* runtime: emit a temp */
                            char* tmp = genvar();
                            sprintf(imcode[code], "%d %s = (%s) %s\n", code, tmp, param_base, arg->str);
                            code++;
                            strcpy(push_str, tmp);
                        }
                    }
                    sprintf(imcode[code], "%d PushParam %s\n", code, push_str);
                    code++;
                    arg = arg->next;
                    param = param->next;
                    arg_idx++;
                }
                sprintf(imcode[code], "%d Call %s\n", code, $2);
                code++;
            }
        }
        $$ = createBoolNode();
    }
}
| CALL IDEN '(' ')' '$' {
    if(!e){
        Function* f = findFunction($2);
        if(f == NULL){
            e=1;
            sprintf(err+strlen(err), "Function %s not declared\n", $2);
        } else {
            if(f->param_count != 0){
                e=1;
                sprintf(err+strlen(err),
                    "Function %s expects %d arguments, got 0\n",
                    $2, f->param_count);
            } else {
                sprintf(imcode[code], "%d Call %s\n", code, $2);
                code++;
            }
        }
        $$ = createBoolNode();
    }
}
|PRINT '(' EXPR ')' '$' {
    if (!e) {
        char* base_type = getBaseType($3->type);
        if(strstr($3->type, "char[") != NULL)
            sprintf(imcode[code], "%d printstring %s\n", code, $3->str);
        else if(strcmp(base_type, "char") == 0)
            sprintf(imcode[code], "%d printchar %s\n", code, $3->str);
        else if(strcmp(base_type, "float") == 0 || strcmp(base_type, "double") == 0)
            sprintf(imcode[code], "%d printfloat %s\n", code, $3->str);
        else
            sprintf(imcode[code], "%d printint %s\n", code, $3->str);
        code++;
        $$ = createBoolNode();
    }
}
|INPUT '(' EXPR ')' '$' {
    if (!e) {
        if(!$3->lv) {
            e = 1;
            sprintf(err + strlen(err), "Input requires a variable, not an expression\n");
        } 
        else {
        char* base_type = getBaseType($3->type);
        if(strstr($3->type, "char[") != NULL)
            sprintf(imcode[code], "%d inputstring %s\n", code, $3->str);
        else if(strcmp(base_type, "char") == 0)
            sprintf(imcode[code], "%d inputchar %s\n", code, $3->str);
        else if(strcmp(base_type, "float") == 0 || strcmp(base_type, "double") == 0)
            sprintf(imcode[code], "%d inputfloat %s\n", code, $3->str);
        else
            sprintf(imcode[code], "%d inputint %s\n", code, $3->str);
        code++;
        $$ = createBoolNode();
    }
}
}
| ENUM { _enum_next_val = 0; } '{' ENUM_MEMBER_LIST '}' '$' {
    if (!e) {
        $$ = createBoolNode();
    }
}
| ASNEXPR '$' {if (!e){$$ = $1;}}
        | ASNEXPR error MEOF{strcat(err,"$ missing\n");yyerrok;e=1;
                                                        //printf("%s\nRejected -> %s -> Could not generate Three Address Code / Storage Layout\n",buffer,err);
                                                        YYACCEPT;}
        | IF '(' BOOLEXPR ')' M  A {if (!e){backpatch($3->T,$5);
                                                                                $$ = createBoolNode();
                                                                                $$->N = merge($3->F,$6->N);
                                                                                $$->B = $6->B;
                                                                                $$->C = $6->C;
                                                                                }}
        | IF '(' BOOLEXPR ')' M A ELSE NN M A {if (!e){
                backpatch($3->T,$5);
                backpatch($3->F,$9);
                $$ = createBoolNode();
                $$->N = merge(merge($6->N,$8->N),$10->N);
                $$->B = merge($6->B, $10->B);
                $$->C = merge($6->C, $10->C);
        }}
        | EXPR error MEOF{{strcat(err,"$ missing");yyerrok;e=1;}
                                                        //printf("%s\nRejected -> %s -> Could not generate Three Address Code / Storage Layout\n",buffer,err);
                                                        YYACCEPT;}
        | IF BOOLEXPR ')' M A ELSE NN M A{{strcat(err,"missing (\n");e=1;}}

        | WHILE M '(' BOOLEXPR ')' M {loop_depth++;} A {if (!e){
    loop_depth--;
    backpatch($8->N,$2);
    backpatch($8->C, $2);
    backpatch($4->T,$6);
    sprintf(imcode[code],"%d goto %d\n",code,$2);
    code++;
    backpatch($8->B, code);
    $$ = createBoolNode();
    $$->N = $4->F;
}}
        | WHILE M  BOOLEXPR ')' M A{{strcat(err,"missing (\n");e=1;}}

        | DO M {loop_depth++;} A WHILE M '(' BOOLEXPR ')' '$' {
    if (!e) {
        loop_depth--;
        backpatch($4->N, $6); 
        backpatch($4->C, $6); 
        backpatch($8->T, $2);
        backpatch($4->B, code);
        backpatch($8->F, code);
        $$ = createBoolNode();
        $$->N = NULL;
    }
}
        | FOR '(' ASNEXPR '$' M BOOLEXPR '$' M ASNEXPR 
    { 
        sprintf(imcode[code], "%d goto %d\n", code, $5); 
        code++; 
    } 
  ')' M {loop_depth++;} A 
    {
        if (!e) {
            loop_depth--;
            backpatch($6->T, $12);
            backpatch($14->N, $8);
            backpatch($14->C, $8);
            sprintf(imcode[code], "%d goto %d\n", code, $8);
            code++;
            backpatch($14->B, code);
            $$ = createBoolNode();
            $$->N = $6->F;
        }
    }
|'{' {top = create_env(top,offset);offset=0;} STMNTS '}' {if (!e) {
                                                $$ = createBoolNode();
                                                $$->N = $3->N;
                                                $$->B = $3->B;
                                                $$->C = $3->C;
                                                top = top->prev;
                                                if (!top) offset =0;
                                                else offset = top->prev_offset;
                                                }}
        | '{' '}' {if (!e){$$=createBoolNode();}}
        | EXPR '$'{if (!e) {$$=createBoolNode();}}
        | DECLSTATEMENT {
            if (!e){$$=createBoolNode();}
            } 
 ;

CASE_LIST: CASE_ITEM M CASE_LIST {
       if(!e) {
           backpatch($1->N, $2);
           $$ = createBoolNode();
           $$->N = $3->N;
           $$->B = merge($1->B, $3->B);
       }
   }
   | CASE_ITEM {
       if(!e) { $$ = $1; }
   };

   CASE_ITEM: CASE CASE_EXPR ':' M {
       if(!e) {
           sprintf(imcode[code], "%d if %s != %s goto ", code, 
                   current_switch_var, $2->str);
           $<addr>$ = code;
           code++;
       }
   } STMNTS {
       if(!e) {
           $$ = createBoolNode();
           $$->N = createNode($<addr>5);
           $$->B = $6->B;
       }
   }
   | DEFAULT ':' M STMNTS {
       if(!e) {
           $$ = createBoolNode();
           $$->N = NULL;
           $$->B = $4->B;
       }
   };

   CASE_EXPR: NUM {
       if(!e) {
           $$ = createExpr();
           strcpy($$->str, $1);
           if(checkfloat($1)) strcpy($$->type, "float");
           else strcpy($$->type, "int");
       }
   }
   | CHARR {
       if(!e) {
           $$ = createExpr();
           strcpy($$->str, $1);
           strcpy($$->type, "char");
       }
   };






DECLSTATEMENT: TYPE DECLLIST '$' {
        struct Decl* temp = $2;
        while(temp){
            char clean_type[100];
            strcpy(clean_type, $1->str);
            if (clean_type[0] == '@') memmove(clean_type, clean_type+1, strlen(clean_type));

            if (temp->re){
                e = 1;
                Symbol* s = get(top->table, temp->key);
                char* decl_type = $1->str;
                if (decl_type[0] == '@') decl_type++;  // strip @
                
                if (strcmp(s->type, decl_type) == 0){
                    sprintf(err + strlen(err), "Redeclaration of %s\n", s->name);
                } else {
                    sprintf(err + strlen(err), "Conflicting types for %s\n", s->name);
                }
            }
            
            if (strcmp(temp->type,"")==0){
                Symbol* s = get(top->table,temp->key);
                s->offset = offset;
                offset+=$1->size;
                strcpy(s->type, clean_type);
                s->dim_count = 0;
            }
            else{
                Symbol* s = get(top->table,temp->key);
                s->offset = offset;
                offset+=(temp->size*$1->size);
                sprintf(s->type,"%s[%d]", clean_type, temp->size);
                s->dim_count = 0;
                char dim_str[1000]; strcpy(dim_str, temp->type);
                char* token = strtok(dim_str, " ");
                if (token && strcmp(token, "array") == 0) token = strtok(NULL, " ");
                int dims[10];
                while(token != NULL && s->dim_count < 10) {
                    int dim = atoi(token);
                    if (dim > 0) { dims[s->dim_count]=dim; s->dimensions[s->dim_count]=dim; s->dim_count++; }
                    token = strtok(NULL, " ");
                }
                if(s->dim_count == 0) sprintf(s->type,"%s[%d]", clean_type, temp->size);
                else if(s->dim_count == 1) sprintf(s->type,"%s[%d]", clean_type, dims[0]);
                else {
                    strcpy(s->type, clean_type);
                    for(int i = 0; i < s->dim_count; i++){ char dim_part[20]; sprintf(dim_part,"[%d]",dims[i]); strcat(s->type,dim_part); }
                }
            }

             if (strcmp(temp->lt,"u")!=0 && strcmp(temp->lt,"array_init")!=0
                    && strcmp(temp->lt,"void")==0) {
                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: Cannot assign void expression to variable '%s'\n", yylineno, temp->key);
                break;  /* stop loop — empty op string would segfault */
            }

            /* ── pointer type safety on declaration init ── */
            if (!e && strcmp(temp->lt,"u")!=0 && strcmp(temp->lt,"array_init")!=0
                    && strcmp(temp->lt,"void")!=0) {
                int decl_is_ptr = isPointerType(clean_type);
                int init_is_real_ptr = (strncmp(temp->lt, "ptr:", 4) == 0);
                if (decl_is_ptr && !init_is_real_ptr) {
                    if (!(strcmp(temp->op,"0")==0 || strcmp(temp->op,"0.0")==0)) {
                        e = 1;
                        sprintf(err+strlen(err),
                            "Line %d: Type error: cannot initialise pointer '%s' (type '%s') with non-pointer value\n",
                            yylineno, temp->key, clean_type);
                        break;
                    }
                } else if (!decl_is_ptr && init_is_real_ptr) {
                    e = 1;
                    sprintf(err+strlen(err),
                        "Line %d: Type error: cannot initialise non-pointer '%s' (type '%s') with pointer value\n",
                        yylineno, temp->key, clean_type);
                    break;
                } else if (decl_is_ptr && init_is_real_ptr && strcmp(clean_type, temp->lt) != 0) {
                    sprintf(err+strlen(err),
                        "Line %d: Warning: pointer type mismatch: initialising '%s' (type '%s') with value of type '%s'\n",
                        yylineno, temp->key, clean_type, temp->lt);
                }
            }

            if (e) break;  /* abort loop if any earlier check set e=1 */

            if (strcmp(temp->lt,"u")==0){ /* no init */ }
            else if (strcmp(temp->lt,"array_init")==0){
                Symbol* s = get(top->table, temp->key);
                char init_copy[1000]; strcpy(init_copy, temp->op);
                char* token = strtok(init_copy, ",");
                int idx = 0;
                int elem_size = 4;
                char* base_type = getBaseType(s->type);
                if (strcmp(base_type,"char")==0) elem_size=1;
                else if (strcmp(base_type,"short")==0) elem_size=2;
                else if (strcmp(base_type,"int")==0||strcmp(base_type,"float")==0) elem_size=4;
                else if (strcmp(base_type,"long")==0||strcmp(base_type,"double")==0) elem_size=8;

                /*  validate init list size */
                int init_count = 0;
                char* count_ptr = temp->op;
                while(*count_ptr){ if(*count_ptr==',') init_count++; count_ptr++; }
                if(strlen(temp->op)>0) init_count++;  /* count = commas + 1 */
                if(init_count > temp->size){
                    e=1;
                    sprintf(err+strlen(err),"Too many initializers for array %s (expected %d, got %d)\n",
                            temp->key, temp->size, init_count);
                }

                /* NEW: Check each array element for range overflow */
                char check_copy[1000]; strcpy(check_copy, temp->op);
                char* check_token = strtok(check_copy, ",");
                int check_idx = 0;
             char fixed_op[1000]; fixed_op[0] = '\0';
                while(check_token != NULL){
                    // Trim whitespace
                    while(*check_token == ' ') check_token++;
                    char* end = check_token + strlen(check_token) - 1;
                    while(end > check_token && *end == ' ') { *end = '\0'; end--; }
                    
                    // Check range for this element
                    char current_val[50];
                    strcpy(current_val, check_token); /* default: keep original */
                    if(isNumericConstant(check_token)){
                        double elem_val = atof(check_token);
                        if(strcmp(base_type,"char")==0 && (elem_val < -128 || elem_val > 127)){
                            int wrapped = (int)elem_val & 0xFF;
                            if(wrapped > 127) wrapped -= 256;
                            sprintf(err+strlen(err),
                                "Warning: Array element %.0f at index %d out of range for char [-128, 127] in '%s' (will wrap to %d)\n",
                                elem_val, check_idx, temp->key, wrapped);
                            sprintf(current_val, "%d", wrapped);
                        }
                        else if(strcmp(base_type,"short")==0 && (elem_val < -32768 || elem_val > 32767)){
                            int wrapped = (int)elem_val & 0xFFFF;
                            if(wrapped > 32767) wrapped -= 65536;
                            sprintf(err+strlen(err),
                                "Warning: Array element %.0f at index %d out of range for short [-32768, 32767] in '%s' (will wrap to %d)\n",
                                elem_val, check_idx, temp->key, wrapped);
                            sprintf(current_val, "%d", wrapped);
                        }
                        else if(strcmp(base_type,"int")==0 && (elem_val < -2147483648.0 || elem_val > 2147483647.0)){
                            long long wrapped = (long long)elem_val & 0xFFFFFFFF;
                            if(wrapped > 2147483647LL) wrapped -= 4294967296LL;
                            sprintf(err+strlen(err),
                                "Warning: Array element %.0f at index %d out of range for int in '%s' (will wrap to %lld)\n",
                                elem_val, check_idx, temp->key, wrapped);
                            sprintf(current_val, "%lld", wrapped);
                        }
                        else if(strcmp(base_type,"float")==0){
                            if(elem_val > FLT_MAX || elem_val < -FLT_MAX){
                                sprintf(err+strlen(err),
                                    "Warning: Array element %g at index %d overflows float in '%s' (will be inf)\n",
                                    elem_val, check_idx, temp->key);
                                sprintf(current_val, "inf");
                            }
                            else if(elem_val != 0.0 && fabs(elem_val) < FLT_MIN){
                                sprintf(err+strlen(err),
                                    "Warning: Array element %g at index %d underflows float in '%s' (will be 0)\n",
                                    elem_val, check_idx, temp->key);
                                sprintf(current_val, "0.0");
                            }
                        }
                        else if(strcmp(base_type,"double")==0){
                            if(isinf(elem_val) || elem_val > DBL_MAX || elem_val < -DBL_MAX){
                                sprintf(err+strlen(err),
                                    "Warning: Array element %g at index %d overflows double in '%s' (will be inf)\n",
                                    elem_val, check_idx, temp->key);
                                sprintf(current_val, "inf");
                            }
                            else if(elem_val != 0.0 && fabs(elem_val) < DBL_MIN){
                                sprintf(err+strlen(err),
                                    "Warning: Array element %g at index %d underflows double in '%s' (will be 0)\n",
                                    elem_val, check_idx, temp->key);
                                sprintf(current_val, "0.0");
                            }
                        }
                    }
                    if(check_idx > 0) strcat(fixed_op, ",");
                    strcat(fixed_op, current_val);
                    check_token = strtok(NULL, ",");
                    check_idx++;
                }
                strcpy(temp->op, fixed_op);               
                /* Generate TAC for array initialization */
                strcpy(init_copy, temp->op);
                token = strtok(init_copy, ",");
                idx = 0;
                while(token != NULL){
                    int byte_offset = idx * elem_size;
                    sprintf(imcode[code], "%d %s[%d] = %s\n", code, temp->key, byte_offset, token);
                    code++;
                    idx++;
                    token = strtok(NULL, ",");
                }
            }
            else if (strcmp(clean_type,temp->lt)==0){
    validateNumericLiteral(temp->op, clean_type, temp->key);
    if(isNumericConstant(temp->op)){
        double val = atof(temp->op);
        if(strcmp(clean_type,"char")==0)
            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(signed char)(long long)val);
        else if(strcmp(clean_type,"short")==0)
            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(short)(long long)val);
        else if(strcmp(clean_type,"int")==0)
            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(int)(long long)val);
        else if(strcmp(clean_type,"long")==0)
            sprintf(imcode[code],"%d %s = %ld\n",code,temp->key,(long)(long long)val);
        else if(strcmp(clean_type,"float")==0)
            sprintf(imcode[code],"%d %s = %g\n",code,temp->key,(float)val);
        else if(strcmp(clean_type,"double")==0)
            sprintf(imcode[code],"%d %s = %g\n",code,temp->key,val);
        else
            sprintf(imcode[code],"%d %s = %s\n",code,temp->key,temp->op);
    } else {
        sprintf(imcode[code],"%d %s = %s\n",code,temp->key,temp->op);
    }
    code++;
}

            else if (strcmp(temp->lt,"char*")==0 && strcmp(clean_type,"char")==0 &&
                     strstr(get(top->table,temp->key)->type, "char[") != NULL){
                Symbol* s = get(top->table,temp->key);
                
                /* Check string length against array size */
                int string_len = temp->str_len;
                int array_size = temp->size;
                if (string_len > array_size) {
                    e = 1;
                    sprintf(err+strlen(err), "Too many initializers: string literal requires %d bytes, but array '%s' has only %d bytes\n", 
                            string_len, temp->key, array_size);
                } else {
                    char str_copy[1000]; strcpy(str_copy, temp->op);
                    int len = strlen(str_copy);
                    if(str_copy[0]=='"' && str_copy[len-1]=='"'){
                        str_copy[len-1]='\0';
                        char* str_content = str_copy + 1;
                        int idx = 0;
                        while(*str_content != '\0'){
                            sprintf(imcode[code], "%d %s[%d] = '%c'\n", code, temp->key, idx, *str_content);
                            code++; str_content++; idx++;
                        }
                        sprintf(imcode[code], "%d %s[%d] = '\\0'\n", code, temp->key, idx);
                        code++;
                    }
                }
            }
            else {
                /* Types don't match - need conversion */
                char base_type[100]; strcpy(base_type, clean_type);
                char* actual_type = base_type;
                if(strncmp(base_type,"const ",6)==0) actual_type = base_type+6;

                /* Also strip const from RHS type */
                char rhs_type[100]; strcpy(rhs_type, temp->lt);
                char* rhs_actual = rhs_type;
                if(strncmp(rhs_type,"const ",6)==0) rhs_actual = rhs_type+6;

                if(strcmp(actual_type, rhs_actual)==0){
                    /* Types match exactly - no cast needed */
                    sprintf(imcode[code],"%d %s = %s\n",code,temp->key,temp->op);
                    code++;
                }
                else {
                    /* NEW: Enhanced type checking and range validation */
                    if(temp->is_literal && isNumericConstant(temp->op)){
                        validateNumericLiteral(temp->op, actual_type, temp->key);
                        double val = atof(temp->op);
                        
                        /* Check ranges and generate appropriate code */
                        if(strcmp(actual_type,"char")==0){
                            if(val < -128 || val > 127){
                                sprintf(err+strlen(err),
                                    "Warning: Value %.0f out of range for char [-128, 127] in '%s' (will wrap to %d)\n",
                                    val, temp->key, (char)(int)val);
                            }
                            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(char)(int)val);
                        }
                        else if(strcmp(actual_type,"short")==0){
                            if(val < -32768 || val > 32767){
                                sprintf(err+strlen(err),
                                    "Warning: Value %.0f out of range for short [-32768, 32767] in '%s' (will wrap to %d)\n",
                                    val, temp->key, (short)(int)val);
                            }
                            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(short)(int)val);
                        }
                       
                        else if(strcmp(actual_type,"int")==0){
    if(val < -2147483648.0 || val > 2147483647.0){
        sprintf(err+strlen(err),
            "Warning: Value %.0f out of range for int [-2147483648, 2147483647] in '%s' (will wrap to %d)\n",
            val, temp->key, (int)(long long)val);
    }
    sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(int)(long long)val);
}

                        else if(strcmp(actual_type,"long")==0){
    if(val > 9223372036854775807.0 || val < -9223372036854775808.0){
        sprintf(err+strlen(err),
            "Warning: Value %.0f out of range for long in '%s' (will wrap)\n",
            val, temp->key);
    }
    sprintf(imcode[code],"%d %s = %ld\n",code,temp->key,(long)(long long)val);
}
                        else if(strcmp(actual_type,"float")==0){
    float fval = (float)val;
    if(isinf(fval) && !isinf(val))
        sprintf(err+strlen(err),
            "Warning: Value %g for '%s' overflows float (stored as inf)\n",
            val, temp->key);
    sprintf(imcode[code],"%d %s = %g\n",code,temp->key,fval);
}
else if(strcmp(actual_type,"double")==0){
    /* double is our storage type already - just emit */
    sprintf(imcode[code],"%d %s = %g\n",code,temp->key,val);
}
                        else{
                            sprintf(imcode[code],"%d %s = (%s) %s\n",code,temp->key,actual_type,temp->op);
                        }
                        code++;
                    } else {
                        /* Non-literal: check for type compatibility warnings */
                        int target_rank = getTypeRank(actual_type);
                        int source_rank = getTypeRank(rhs_actual);
                        
                        if(target_rank > 0 && source_rank > 0 && source_rank > target_rank){
                            sprintf(err+strlen(err),
                                "Warning: Narrowing conversion from %s to %s in '%s'\n",
                                rhs_actual, actual_type, temp->key);
                        }
                        
                        if(isFloatingType(rhs_actual) && isIntegerType(actual_type)){
                            sprintf(err+strlen(err),
                                "Warning: Conversion from %s to %s will discard fractional part in '%s'\n",
                                rhs_actual, actual_type, temp->key);
                        }
                        
                        sprintf(imcode[code],"%d %s = (%s) %s\n",code,temp->key,actual_type,temp->op);
                        code++;
                    }
                }
            }
            temp = temp->next;
        }
}
| TYPE DECLLIST  error MEOF{{strcat(err,"$ missing\n");yyerrok;e=1;}
                                                        //printf("%s\nRejected -> %s -> Could not generate Three Address Code / Storage Layout\n",buffer,err);
                                                        YYACCEPT; }
;




/* ── Enum member list rules ──
   Uses a global counter so "enum { A, B, C }" assigns 0,1,2
   and "enum { X=5, Y, Z }" assigns 5,6,7.
   Enum members are stored as integer constants and can be used
   wherever an int expression is expected.                        */

ENUM_MEMBER_LIST:
    ENUM_MEMBER_LIST ',' ENUM_MEMBER { if(!e){ $$ = createBoolNode(); } }
  | ENUM_MEMBER                      { if(!e){ $$ = createBoolNode(); } }
  ;

ENUM_MEMBER:
    IDEN '=' NUM {
        if (!e) {
            int dummy;
            if (enum_get($1, &dummy)) {
                e = 1;
                sprintf(err+strlen(err), "Duplicate enum constant '%s'\n", $1);
            } else {
                int val = atoi($3);
                _enum_next_val = val + 1;   /* next auto-value follows this */
                enum_put($1, val);
                if (get(top->table, $1) == NULL) {
                    Symbol* s = createSymbol($1);
                    strcpy(s->type, "const int");
                    s->offset = offset;
                    offset += 4;
                    put(top->table, $1, s);
                }
                sprintf(imcode[code], "%d %s = %d\n", code, $1, val);
                code++;
            }
            $$ = createBoolNode();
        }
    }
  | IDEN {
        if (!e) {
            int dummy;
            if (enum_get($1, &dummy)) {
                e = 1;
                sprintf(err+strlen(err), "Duplicate enum constant '%s'\n", $1);
            } else {
                int val = _enum_next_val++;
                enum_put($1, val);
                if (get(top->table, $1) == NULL) {
                    Symbol* s = createSymbol($1);
                    strcpy(s->type, "const int");
                    s->offset = offset;
                    offset += 4;
                    put(top->table, $1, s);
                }
                sprintf(imcode[code], "%d %s = %d\n", code, $1, val);
                code++;
            }
            $$ = createBoolNode();
        }
    }
  ;


INIT_LIST: EXPR ',' INIT_LIST {
        if(!e){ $$ = $1; $$->next = $3; }
    }
    | EXPR { if(!e){ $$ = $1; $$->next = NULL; } };

DECLLIST: IDEN ',' DECLLIST {if (get(top->table,$1)==NULL){
                                                                Symbol* s = createSymbol($1);
                                                                put(top->table,$1,s);
                                                                $$ = createDecl($1);
                                                                $$->next = $3;
                                                        }
                                                        else{
                                                                $$ = createDecl($1);
                                                                strcpy($$->type,"");
                                                                $$->re =1;
                                                                }strcpy($$->lt,"u");
                                                }
        | IDEN INDEX ',' DECLLIST {
                                if (get(top->table,$1)==NULL){
                                        Symbol* s = createSymbol($1);
                                        put(top->table,$1,s);
                                        $$ = createDecl($1);
                                        $$->next = $4;
                                        strcpy($$->type,$2->str);
                                        $$->size = $2->size;
                                }
                                else{
                                        $$ = createDecl($1);
                                        strcpy($$->type,"");
                                        $$->re =1;
                                }strcpy($$->lt,"u");
        }
        | IDEN {if (get(top->table,$1)==NULL){
                                                Symbol* s = createSymbol($1);
                                                put(top->table,$1,s);
                                                $$ = createDecl($1);
                        }
                        else{
                                                $$ = createDecl($1);
                                                strcpy($$->type,"");
                                                $$->re = 1;
                                                }strcpy($$->lt,"u");}
        | IDEN '=' EXPR {
                                        if (get(top->table,$1)==NULL){
                                                Symbol* s = createSymbol($1);
                                                put(top->table,$1,s);
                                                $$ = createDecl($1);
                                                strcpy($$->lt,$3->type);
                                                strcpy($$->op,$3->str);
                                                $$->is_literal = isLiteral($3->str);
                                                }
                                        else{
                                                $$ = createDecl($1);
                                                strcpy($$->type,"");
                                                strcpy($$->lt,$3->type);
                                                strcpy($$->op,$3->str);
                                                $$->is_literal = isLiteral($3->str);
                                                $$->re=1;
                                        }}
 | IDEN '=' EXPR ',' DECLLIST {
                                        if (get(top->table,$1)==NULL){
                                                Symbol* s = createSymbol($1);
                                                put(top->table,$1,s);
                                                $$ = createDecl($1);
                                                strcpy($$->lt,$3->type);
                                                strcpy($$->op,$3->str);
                                                $$->is_literal = isLiteral($3->str);
                                                $$->next = $5;
                                                }
                                        else{
                                                $$ = createDecl($1);
                                                strcpy($$->type,"");
                                                strcpy($$->lt,$3->type);
                                                strcpy($$->op,$3->str);
                                                $$->is_literal = isLiteral($3->str);
                                                $$->re=1;
                                                $$->next = $5;
                                        }}
        | IDEN INDEX {if (get(top->table,$1)==NULL){
                                                Symbol* s = createSymbol($1);
                                                put(top->table,$1,s);
                                                $$ = createDecl($1);
                                                strcpy($$->type,$2->str);
                                                $$->size = $2->size;
                                                }
                                        else{
                                                $$ = createDecl($1);
                                                strcpy($$->type,"");
                                                $$->re=1;
                                        }strcpy($$->lt,"u");}
        | IDEN INDEX '=' '{' INIT_LIST '}' {
        if (get(top->table,$1)==NULL){
            Symbol* s = createSymbol($1);
            put(top->table,$1,s);
            $$ = createDecl($1);
            strcpy($$->type,$2->str);
            $$->size = $2->size;
            strcpy($$->lt,"array_init");
            char init_str[1000] = "";
            struct Expr* e = $5; int idx = 0;
            while(e){ if(idx>0) strcat(init_str,","); strcat(init_str,e->str); e=e->next; idx++; }
            strcpy($$->op, init_str);
        } else {
            $$ = createDecl($1); strcpy($$->type,""); $$->re=1;
        }
    }
    | IDEN INDEX '=' '{' INIT_LIST '}' ',' DECLLIST {
        if (get(top->table,$1)==NULL){
            Symbol* s = createSymbol($1);
            put(top->table,$1,s);
            $$ = createDecl($1);
            strcpy($$->type,$2->str);
            $$->size = $2->size;
            $$->next = $8;
            strcpy($$->lt,"array_init");
            char init_str[1000] = "";
            struct Expr* e = $5; int idx = 0;
            while(e){ if(idx>0) strcat(init_str,","); strcat(init_str,e->str); e=e->next; idx++; }
            strcpy($$->op, init_str);
        } else {
            $$ = createDecl($1); strcpy($$->type,""); $$->re=1; $$->next = $8;
        }
    }
        | IDEN INDEX '=' EXPR {
                if (get(top->table,$1)==NULL){
                    Symbol* s = createSymbol($1);
                    put(top->table,$1,s);
                    $$ = createDecl($1);
                    strcpy($$->type,$2->str);
                    $$->size = $2->size;
                    strcpy($$->lt, $4->type);
                    strcpy($$->op, $4->str);
                    if(strcmp($4->type, "char*") == 0) $$->str_len = $4->str_len;
                    $$->is_literal = 1;
                } else {
                    $$ = createDecl($1); strcpy($$->type,""); $$->re=1;
                }
        }
        | IDEN INDEX '=' EXPR ',' DECLLIST {
                if (get(top->table,$1)==NULL){
                    Symbol* s = createSymbol($1);
                    put(top->table,$1,s);
                    $$ = createDecl($1);
                    strcpy($$->type,$2->str);
                    $$->size = $2->size;
                    $$->next = $6;
                    strcpy($$->lt, $4->type);
                    strcpy($$->op, $4->str);
                    if(strcmp($4->type, "char*") == 0) $$->str_len = $4->str_len;
                    $$->is_literal = 1;
                } else {
                    $$ = createDecl($1); strcpy($$->type,""); $$->re=1; $$->next = $6;
                }
        };

/* added positive-size check */
INDEX: '[' NUM ']' {$$ = createType();
                    int arr_size = atoi($2);
                    /* positive size check*/
                    if(arr_size <= 0){
                        e=1;
                        sprintf(err+strlen(err),"Array size must be positive (got %d)\n", arr_size);
                    }
                    $$->size=arr_size;
                    sprintf($$->str,"array %d ", arr_size);
                    if (checkfloat($2)){
                            e=1;sprintf(err+strlen(err),"Array index cannot be float\n");
                    }}
        | '[' NUM ']' INDEX {$$ = createType();
                             int arr_size = atoi($2);
                             /* positive size check  */
                             if(arr_size <= 0){
                                 e=1;
                                 sprintf(err+strlen(err),"Array size must be positive (got %d)\n", arr_size);
                             }
                             $$->size=$4->size*arr_size;
                             sprintf($$->str,"array %d %s", arr_size, $4->str);
                             if (checkfloat($2)){
                                     e=1;sprintf(err+strlen(err),"Array index cannot be float\n");
                             }};

TYPE: INT {$$ = createType(); strcpy($$->str,$1);$$->size=4;}
        | FLOAT  {$$ = createType();strcpy($$->str,$1);$$->size=4;}
    | BOOL {$$ = createType();strcpy($$->str,$1);$$->size=1;}
        | CHAR {$$ = createType();strcpy($$->str,$1);$$->size=1;}
    | SHORT {$$ = createType();strcpy($$->str,$1);$$->size=2;}
    | LONG {$$ = createType();strcpy($$->str,$1);$$->size=8;}
    | DOUBLE {$$ = createType();strcpy($$->str,$1);$$->size=8;}
    | VOID {$$ = createType();strcpy($$->str,$1);$$->size=0;}
    | PTRTYPE TYPE {
        /* @ptr @int x  →  type "ptr:int", size=8 (pointer width) */
        $$ = createType();
        char pointee[100];
        strcpy(pointee, $2->str);
        if (pointee[0] == '@') memmove(pointee, pointee+1, strlen(pointee)); /* strip @ */
        sprintf($$->str, "ptr:%s", pointee);
        $$->size = 8;
    }
    | CONST TYPE {
    $$ = $2;
    char base[100];
    strcpy(base, $2->str);
    if (base[0] == '@') memmove(base, base+1, strlen(base));
    sprintf($$->str, "const %s", base);
};

  
STMNTS: STMNTS M A {if (!e){backpatch($1->N,$2);
                                        $$ = createBoolNode();
                                        $$->N = $3->N;
                                        $$->B = merge($1->B, $3->B);
                                        $$->C = merge($1->C, $3->C);
}}
        | A M{if (!e){$$ = createBoolNode();
                $$->N = $1->N;
                $$->B = $1->B;
                $$->C = $1->C;
}};


ASSGN: '=' {strcpy($$,"=");}
         | PASN {strcpy($$,$1);}
         | MASN {strcpy($$,$1);}
     | DASN {strcpy($$,$1);}
     | SASN {strcpy($$,$1);}
     | BANDASN {strcpy($$,"&=");}
     | BORASN  {strcpy($$,"|=");}
     | BXORASN {strcpy($$,"^=");}
     | LSHIFTASN {strcpy($$,"<<=");}
     | RSHIFTASN {strcpy($$,">>=");}| MODASN {strcpy($$,"%=");} ;

BOOLEXPR:
         BOOLEXPR OR M BOOLEXPR {  if (!e){backpatch($1->F,$3);
                                                                $$ = createBoolNode();
                                                                $$->T = merge($1->T,$4->T);
                                                                $$->F = $4->F;
                                                         }}
    | BOOLEXPR AND M BOOLEXPR { if (!e){backpatch($1->T,$3);
                                                                $$ = createBoolNode();
                                                                $$->T = $4->T;
                                                                $$->F = merge($1->F,$4->F);
                                                                }}
        | '!' BOOLEXPR {
                if (!e){ $$ = createBoolNode(); $$->T = $2->F; $$->F = $2->T; }
        }
        | '(' BOOLEXPR ')' {
                if (!e){ $$ = createBoolNode(); $$->T = $2->T; $$->F = $2->F; }
        }
        | EXPR LT EXPR  {if(!e) {sprintf(imcode[code],"%d if %s %s %s goto ",code,$1->str,$2,$3->str);
                                                        $$ = createBoolNode();
                                                        $$->T = createNode(code); code++;
                                                        sprintf(imcode[code],"%d goto ",code);
                                                        $$->F = createNode(code); code++;}}
    | EXPR GT EXPR  {if(!e) {sprintf(imcode[code],"%d if %s %s %s goto ",code,$1->str,$2,$3->str);
                                                        $$ = createBoolNode();
                                                        $$->T = createNode(code); code++;
                                                        sprintf(imcode[code],"%d goto ",code);
                                                        $$->F = createNode(code); code++;}}
        | EXPR EQ EXPR  {if(!e) {sprintf(imcode[code],"%d if %s %s %s goto ",code,$1->str,$2,$3->str);
                                                        $$ = createBoolNode();
                                                        $$->T = createNode(code); code++;
                                                        sprintf(imcode[code],"%d goto ",code);
                                                        $$->F = createNode(code); code++;}}
    | EXPR NE EXPR  {if(!e) {sprintf(imcode[code],"%d if %s %s %s goto ",code,$1->str,$2,$3->str);
                                                        $$ = createBoolNode();
                                                        $$->T = createNode(code); code++;
                                                        sprintf(imcode[code],"%d goto ",code);
                                                        $$->F = createNode(code); code++;}}
        | EXPR LE EXPR  {if(!e) {sprintf(imcode[code],"%d if %s %s %s goto ",code,$1->str,$2,$3->str);
                                                        $$ = createBoolNode();
                                                        $$->T = createNode(code); code++;
                                                        sprintf(imcode[code],"%d goto ",code);
                                                        $$->F = createNode(code); code++;}}
    | EXPR GE EXPR  {if(!e) {sprintf(imcode[code],"%d if %s %s %s goto ",code,$1->str,$2,$3->str);
                                                        $$ = createBoolNode();
                                                        $$->T = createNode(code); code++;
                                                        sprintf(imcode[code],"%d goto ",code);
                                                        $$->F = createNode(code); code++;}}
        | TR {if (!e){
                $$ = createBoolNode();
                $$->T = createNode(code);
                sprintf(imcode[code],"%d goto ",code);
                code++;
        }}
        | FL {if (!e){
                $$ = createBoolNode();
                $$->F = createNode(code);
                sprintf(imcode[code],"%d goto ",code);
                code++;
        }};


M: {$$=code;};
NN: {$$=createBoolNode();
        $$->N = createNode(code);
        sprintf(imcode[code],"%d goto ",code);
        code++;
        };


ASNEXPR: BANDASN {strcpy($$, "&=");}
     | BORASN {strcpy($$, "|=");}
     | BXORASN {strcpy($$, "^=");}
     | LSHIFTASN {strcpy($$, "<<=");}
     | RSHIFTASN {strcpy($$, ">>=");}
|EXPR ASSGN EXPR {
    if (!e && $1->lv){
         if(strcmp($3->type, "void")==0){
            e=1;
            sprintf(err+strlen(err), "Cannot assign void expression to '%s'\n", $1->str);
        }

        /* ── pointer type safety check ── */
        if (!e) {
            int lhs_is_ptr = isPointerType($1->type);
            int rhs_is_ptr = isPointerType($3->type);
            if (lhs_is_ptr && !rhs_is_ptr) {
                if (!(strcmp($3->str,"0")==0 || strcmp($3->str,"0.0")==0)) {
                    e = 1;
                    sprintf(err+strlen(err),
                        "Line %d: Type error: cannot assign non-pointer '%s' to pointer variable of type '%s'\n",
                        yylineno, $3->str, $1->type);
                }
            } else if (!lhs_is_ptr && rhs_is_ptr) {
                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: Type error: cannot assign pointer '%s' to non-pointer variable of type '%s'\n",
                    yylineno, $3->str, $1->type);
            } else if (lhs_is_ptr && rhs_is_ptr && strcmp($1->type, $3->type) != 0) {
                sprintf(err+strlen(err),
                    "Line %d: Warning: pointer type mismatch: assigning '%s' to '%s'\n",
                    yylineno, $3->type, $1->type);
            }
        }

        /* ── pointer write: if LHS was produced by 'deref PTR', emit a store-through-ptr ── */
        if ($1->is_deref && !e) {
            if (strlen($2) != 1 || $2[0] != '=') {
                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: Compound assignment through pointer not supported; use simple '='\n",
                    yylineno);
            } else {
                /* The DEREF IDEN rule already emitted "tN = deref PTR" as a read temp.
                   Since this is a write (store-through-pointer), that read is spurious —
                   erase it (reclaim the slot) and emit the real store instead. */
                if (code > 0) {
                    char _prev[10000]; strcpy(_prev, imcode[code-1]);
                    char _plhs[200]; int _pln;
                    if (sscanf(_prev, "%d %199s =", &_pln, _plhs) == 2 &&
                        strncmp(_plhs, "t", 1) == 0) {
                        /* It's the phantom read temp — erase it and reclaim the slot */
                        imcode[code-1][0] = '\0';
                        code--;
                    }
                }
                sprintf(imcode[code], "%d deref %s = %s\n", code, $1->deref_src, $3->str);
                code++;
            }
            $$ = createBoolNode();
        } else {
        Symbol* sym = env_get(top, $1->str);
        if(sym && strstr(sym->type, "const") != NULL){
            e=1;
            sprintf(err+strlen(err), "Cannot assign to const variable %s\n", $1->str);
        }

        if (strcmp($3->type, "char*") == 0 && 
            strstr($1->type, "char[") != NULL &&
            strlen($2)==1 && $2[0]=='=') {
            char* bracket = strchr($1->type, '[');
            if (bracket) {
                int array_size = atoi(bracket + 1);
                int string_len = $3->str_len;
                if (string_len > array_size) {
                    e = 1;
                    sprintf(err+strlen(err), "String literal too large for array (needs %d bytes, array is %d bytes)\n", string_len, array_size);
                } else {
                    char str_copy[1000]; strcpy(str_copy, $3->str);
                    int len = strlen(str_copy);
                    if(str_copy[0]=='"' && str_copy[len-1]=='"'){
                        str_copy[len-1]='\0';
                        char* str_content = str_copy + 1;
                        int idx = 0;
                        while(*str_content != '\0'){
                            sprintf(imcode[code], "%d %s[%d] = '%c'\n", code, $1->str, idx, *str_content);
                            code++; str_content++; idx++;
                        }
                        sprintf(imcode[code], "%d %s[%d] = '\\0'\n", code, $1->str, idx);
                        code++;
                    }
                }
            }
            $$ = createBoolNode();
        }
        else {
            if (strlen($2)==1){
                sprintf(imcode[code],"%d %s = %s\n",code,$1->str,$3->str);
                code++;
            }
            else{
    char* t = genvar();
    /* Strip trailing '=' to get the actual operator */
    char op_only[10];
    strncpy(op_only, $2, sizeof(op_only)-1);
    op_only[sizeof(op_only)-1] = '\0';
    int op_len = strlen(op_only);
    if (op_len > 0 && op_only[op_len-1] == '=') op_only[op_len-1] = '\0';

    /* Get LHS variable type from symbol table */
    Symbol* lhs_sym = env_get(top, $1->str);
    char lhs_type[100] = "";
    if(lhs_sym) strcpy(lhs_type, getBaseType(lhs_sym->type));

    /* Determine promoted type for the operation */
    char lhs_base[100], rhs_base[100];
    strcpy(lhs_base, lhs_type[0] ? lhs_type : $1->type);
    strcpy(rhs_base, getBaseType($3->type));
    char* promoted = promoteType(lhs_base, rhs_base);

    /* Bitwise ops: warn if used on float/double */
    if((strcmp(op_only,"&")==0||strcmp(op_only,"|")==0||strcmp(op_only,"^")==0||
        strcmp(op_only,"<<")==0||strcmp(op_only,">>")==0) &&
       (isFloatingType(lhs_base)||isFloatingType(rhs_base))){
        e=1;
        sprintf(err+strlen(err),
            "Error: Bitwise operator '%s=' cannot be applied to float/double types\n", op_only);
    } else {
        /* Cast LHS up to promoted type if needed */
        char lhs_str[100]; strcpy(lhs_str, $1->str);
        if(strcmp(lhs_base, promoted) != 0){
            char* cl = genvar();
            sprintf(imcode[code],"%d %s = (%s) %s\n",code,cl,promoted,$1->str); code++;
            strcpy(lhs_str, cl);
        }

        /* Cast RHS up to promoted type if needed */
        char rhs_str[100]; strcpy(rhs_str, $3->str);
        if(strcmp(rhs_base, promoted) != 0){
            char* cr = genvar();
            sprintf(imcode[code],"%d %s = (%s) %s\n",code,cr,promoted,$3->str); code++;
            strcpy(rhs_str, cr);
        }

        /* Perform the operation */
        sprintf(imcode[code],"%d %s = %s %s %s\n",code,t,lhs_str,op_only,rhs_str); code++;

        /* Cast result back to LHS type if it differs from promoted type */
        if(strcmp(lhs_base, promoted) != 0){
            /* narrowing: warn */
            sprintf(err+strlen(err),
                "Warning: Implicit narrowing conversion from %s to %s in compound assignment to '%s'\n",
                promoted, lhs_base, $1->str);
            char* cback = genvar();
            sprintf(imcode[code],"%d %s = (%s) %s\n",code,cback,lhs_base,t); code++;
            sprintf(imcode[code],"%d %s = %s\n",code,$1->str,cback); code++;
        } else {
            sprintf(imcode[code],"%d %s = %s\n",code,$1->str,t); code++;
        }
    }
}
            $$ = createBoolNode();
        }
        } /* end else (non-deref assignment) */
    }
    if (!$1->lv){e=1;strcat(err,"L value not assignable\n");}
}

/* EXPR: division/modulo by zero checks added */
EXPR: SIZEOF '(' IDEN ')' {
    if(!e){
        $$ = createExpr();
        Env* temp = top; int found = 0; int var_size = 4;
        while(temp){
            Symbol* sym = get(temp->table, $3);
            if(sym){
                found = 1;
                char* base_type = getBaseType(sym->type);
                if(strcmp(base_type,"char")==0) var_size=1;
                else if(strcmp(base_type,"short")==0) var_size=2;
                else if(strcmp(base_type,"int")==0||strcmp(base_type,"float")==0) var_size=4;
                else if(strcmp(base_type,"long")==0||strcmp(base_type,"double")==0) var_size=8;
                if(sym->dim_count > 0){
                    int total_elements = 1;
                    for(int i = 0; i < sym->dim_count; i++) total_elements *= sym->dimensions[i];
                    var_size *= total_elements;
                }
                break;
            }
            temp = temp->prev;
        }
        if(!found){ e=1; sprintf(err+strlen(err), "%s is not declared in scope\n", $3); }
        sprintf($$->str, "%d", var_size);
        strcpy($$->type, "int");
        $$->lv = 0;
    }
}
| SIZEOF '(' TYPE ')' {
    /* getsizeof(@T) — static size of a type */
    if(!e){
        $$ = createExpr();
        char clean_t[100]; strcpy(clean_t, $3->str);
        if(clean_t[0]=='@') memmove(clean_t, clean_t+1, strlen(clean_t));
        int tsz = 4;
        if(strcmp(clean_t,"char")==0)   tsz=1;
        else if(strcmp(clean_t,"short")==0) tsz=2;
        else if(strcmp(clean_t,"int")==0||strcmp(clean_t,"float")==0) tsz=4;
        else if(strcmp(clean_t,"long")==0||strcmp(clean_t,"double")==0) tsz=8;
        else if(strncmp(clean_t,"ptr:",4)==0) tsz=8;
        sprintf($$->str, "%d", tsz);
        strcpy($$->type, "int");
        $$->lv = 0;
    }
}


| ABS '(' EXPR ')' {
    if (!e) {
        $$ = createExpr();
        char arg[1000]; strcpy(arg, $3->str);
        char* arg_type = getBaseType($3->type);
        strcpy($$->type, arg_type);
        $$->lv = 0;
        if (isNumericConstant(arg)) {
            double v = atof(arg);
            if (v < 0) v = -v;
            if (isFloatingType(arg_type))
                sprintf($$->str, "%g", v);
            else
                sprintf($$->str, "%d", (int)v);
        } else {
            /* C0: res = arg  (assume positive)
               C1: if arg >= 0 goto C4
               C2: neg = 0 - arg
               C3: res = neg
               C4: done */
            char* res = genvar();
            char* neg = genvar();
            strcpy($$->str, res);
            sprintf(imcode[code], "%d %s = %s\n", code, res, arg); code++;
            int C1 = code;
            sprintf(imcode[code], "%d if %s >= 0 goto ", code, arg); code++;
            sprintf(imcode[code], "%d %s = 0 - %s\n", code, neg, arg); code++;
            sprintf(imcode[code], "%d %s = %s\n", code, res, neg); code++;
            int C4 = code;
            int len1 = strlen(imcode[C1]);
            if (imcode[C1][len1-1] != '\n')
                sprintf(imcode[C1] + len1, "%d\n", C4);
        }
    }
}
/* ── built-in min(x, y, z, ...) ─────────────────────────────────────────
   min(arglist) → smallest value among all arguments.
   Uses ARGLIST so it already handles 1..N args via the linked list.
   TAC: linear scan — compare each subsequent arg against running minimum.
   ─────────────────────────────────────────────────────────────────────── */
| MIN '(' ARGLIST ')' {
    if (!e) {
        $$ = createExpr();
        struct Expr* args = $3;
        if (args == NULL) {
            e = 1;
            sprintf(err + strlen(err), "min() requires at least one argument\n");
            strcpy($$->str, "0"); strcpy($$->type, "int"); $$->lv = 0;
        } else {
            char res_type[100];
            strcpy(res_type, getBaseType(args->type));
            struct Expr* scan = args->next;
            while (scan) {
                char* pt = promoteType(res_type, getBaseType(scan->type));
                strcpy(res_type, pt);
                scan = scan->next;
            }
            strcpy($$->type, res_type);
            $$->lv = 0;
            if (args->next == NULL) {
                strcpy($$->str, args->str);
            } else {
                /* Running min in cur_min.
                   For each next arg:
                     C_cmp: if cur_min <= arg goto C_skip
                     C_upd: cur_min = arg
                     C_skip: (next iteration)                */
                char* cur_min = genvar();
                sprintf(imcode[code], "%d %s = %s\n", code, cur_min, args->str); code++;
                scan = args->next;
                while (scan) {
                    char arg_copy[1000]; strcpy(arg_copy, scan->str);
                    int C_cmp = code;
                    sprintf(imcode[code], "%d if %s <= %s goto ", code, cur_min, arg_copy); code++;
                    sprintf(imcode[code], "%d %s = %s\n", code, cur_min, arg_copy); code++;
                    int C_skip = code;
                    int len2 = strlen(imcode[C_cmp]);
                    if (imcode[C_cmp][len2-1] != '\n')
                        sprintf(imcode[C_cmp] + len2, "%d\n", C_skip);
                    scan = scan->next;
                }
                strcpy($$->str, cur_min);
            }
        }
    }
}
/* ── built-in max(x, y, z, ...) ─────────────────────────────────────────
   max(arglist) → largest value among all arguments.
   Mirror of min(), comparison direction flipped.
   ─────────────────────────────────────────────────────────────────────── */
| MAX '(' ARGLIST ')' {
    if (!e) {
        $$ = createExpr();
        struct Expr* args = $3;
        if (args == NULL) {
            e = 1;
            sprintf(err + strlen(err), "max() requires at least one argument\n");
            strcpy($$->str, "0"); strcpy($$->type, "int"); $$->lv = 0;
        } else {
            char res_type[100];
            strcpy(res_type, getBaseType(args->type));
            struct Expr* scan = args->next;
            while (scan) {
                char* pt = promoteType(res_type, getBaseType(scan->type));
                strcpy(res_type, pt);
                scan = scan->next;
            }
            strcpy($$->type, res_type);
            $$->lv = 0;
            if (args->next == NULL) {
                strcpy($$->str, args->str);
            } else {
                /* Running max in cur_max.
                   For each next arg:
                     C_cmp: if cur_max >= arg goto C_skip
                     C_upd: cur_max = arg
                     C_skip: (next iteration)                */
                char* cur_max = genvar();
                sprintf(imcode[code], "%d %s = %s\n", code, cur_max, args->str); code++;
                scan = args->next;
                while (scan) {
                    char arg_copy[1000]; strcpy(arg_copy, scan->str);
                    int C_cmp = code;
                    sprintf(imcode[code], "%d if %s >= %s goto ", code, cur_max, arg_copy); code++;
                    sprintf(imcode[code], "%d %s = %s\n", code, cur_max, arg_copy); code++;
                    int C_skip = code;
                    int len3 = strlen(imcode[C_cmp]);
                    if (imcode[C_cmp][len3-1] != '\n')
                        sprintf(imcode[C_cmp] + len3, "%d\n", C_skip);
                    scan = scan->next;
                }
                strcpy($$->str, cur_max);
            }
        }
    }
}
| EXPR '+' EXPR {
    if (!e){
        $$ = createExpr();
        if (tryConstantFold($1, $3, '+', $$)) {
        } else {
            /* Pointer arithmetic: ptr + int  or  int + ptr */
            int l_is_ptr = isPointerType($1->type);
            int r_is_ptr = isPointerType($3->type);
            if (l_is_ptr && !r_is_ptr && isIntegerType(getBaseType($3->type))) {
                /* ptr + int → result has same pointer type as LHS */
                char* t = genvar(); strcpy($$->str, t);
                strcpy($$->type, $1->type);
                sprintf(imcode[code], "%d %s = %s + %s\n", code, t, $1->str, $3->str); code++;
            } else if (!l_is_ptr && r_is_ptr && isIntegerType(getBaseType($1->type))) {
                /* int + ptr → result has same pointer type as RHS */
                char* t = genvar(); strcpy($$->str, t);
                strcpy($$->type, $3->type);
                sprintf(imcode[code], "%d %s = %s + %s\n", code, t, $1->str, $3->str); code++;
            } else {
                char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
                char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
                checkType($1,$3,ct1,ct2,$$->type);
                if(strcmp(ct1,"")){strcpy($1->str,ct1);}
                if(strcmp(ct2,"")){strcpy($3->str,ct2);}
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s + %s\n",code,t,$1->str,$3->str); code++;
            }
        }
        $$->lv=0;
    }
}
| EXPR '-' EXPR {
    if (!e){
        $$ = createExpr();
        if (tryConstantFold($1, $3, '-', $$)) {
        } else {
            /* Pointer arithmetic: ptr - int */
            int l_is_ptr = isPointerType($1->type);
            int r_is_ptr = isPointerType($3->type);
            if (l_is_ptr && !r_is_ptr && isIntegerType(getBaseType($3->type))) {
                /* ptr - int → result has same pointer type */
                char* t = genvar(); strcpy($$->str, t);
                strcpy($$->type, $1->type);
                sprintf(imcode[code], "%d %s = %s - %s\n", code, t, $1->str, $3->str); code++;
            } else {
                char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
                char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
                checkType($1,$3,ct1,ct2,$$->type);
                if(strcmp(ct1,"")){strcpy($1->str,ct1);}
                if(strcmp(ct2,"")){strcpy($3->str,ct2);}
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s - %s\n",code,t,$1->str,$3->str); code++;
            }
        }
        $$->lv=0;
    }
}
| EXPR '*' EXPR {
    if (!e){
        $$ = createExpr();
        if (tryConstantFold($1, $3, '*', $$)) {
        } else {
            char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
            char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
            checkType($1,$3,ct1,ct2,$$->type);
            if(strcmp(ct1,"")){strcpy($1->str,ct1);}
            if(strcmp(ct2,"")){strcpy($3->str,ct2);}
            char* t = genvar(); strcpy($$->str,t);
            sprintf(imcode[code],"%d %s = %s * %s\n",code,t,$1->str,$3->str); code++;
        }
        $$->lv=0;
    }
}
| EXPR '/' EXPR {
    if (!e){
        /*  division by zero check */
        if(isLiteral($3->str) && atof($3->str) == 0.0){
            e=1; sprintf(err+strlen(err),"Division by zero\n");
        }
        $$ = createExpr();
        if (tryConstantFold($1, $3, '/', $$)) {
        } else {
            char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
            char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
            checkType($1,$3,ct1,ct2,$$->type);
            if(strcmp(ct1,"")){strcpy($1->str,ct1);}
            if(strcmp(ct2,"")){strcpy($3->str,ct2);}
            char* t = genvar(); strcpy($$->str,t);
            sprintf(imcode[code],"%d %s = %s / %s\n",code,t,$1->str,$3->str); code++;
        }
        $$->lv=0;
    }
}
| EXPR '%' EXPR {
    if (!e){
        /* modulo by zero check*/
        if(isLiteral($3->str) && atoi($3->str) == 0){
            e=1; sprintf(err+strlen(err),"Modulo by zero\n");
        }
        $$ = createExpr();
        if (tryConstantFold($1, $3, '%', $$)) {
        } else {
            if (isFloatingType($1->type) || isFloatingType($3->type)){
                e=1;
                sprintf(err+strlen(err),"invalid operands to binary %% (float/double)\n");
            }
            char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
            char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
            checkType($1,$3,ct1,ct2,$$->type);
            if(strcmp(ct1,"")){strcpy($1->str,ct1);}
            if(strcmp(ct2,"")){strcpy($3->str,ct2);}
            char* t = genvar(); strcpy($$->str,t);
            sprintf(imcode[code],"%d %s = %s %% %s\n",code,t,$1->str,$3->str); code++;
        }
        $$->lv=0;
    }
}
|'(' EXPR ')'  {if (!e){$$ = createExpr();strcpy($$->str,$2->str); strcpy($$->type,$2->type);$$->lv=$2->lv;}}
        | EXPR OP '$'{e=1;strcpy(err,"Missing operand");yyerrok;}
    | EXPR BAND EXPR {
        if (!e){ 
            $$ = createExpr();
            if (tryConstantFold($1, $3, '&', $$)) { $$->lv = 0; } else {
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err),"invalid operands to bitwise & (float/double)\n"); }
                char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
                char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
                checkType($1,$3,ct1,ct2,$$->type);
                if(strcmp(ct1,"")){strcpy($1->str,ct1);}
                if(strcmp(ct2,"")){strcpy($3->str,ct2);}
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s & %s\n",code,t,$1->str,$3->str); code++;
            }
            $$->lv=0;
        }
    }
    | EXPR BOR EXPR {
        if (!e){ 
            $$ = createExpr();
            if (tryConstantFold($1, $3, '|', $$)) { $$->lv = 0; } else {
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err),"invalid operands to bitwise | (float/double)\n"); }
                char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
                char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
                checkType($1,$3,ct1,ct2,$$->type);
                if(strcmp(ct1,"")){strcpy($1->str,ct1);}
                if(strcmp(ct2,"")){strcpy($3->str,ct2);}
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s | %s\n",code,t,$1->str,$3->str); code++;
            }
            $$->lv=0;
        }
    }
    | EXPR BXOR EXPR {
        if (!e){ 
            $$ = createExpr();
            if (tryConstantFold($1, $3, '^', $$)) { $$->lv = 0; } else {
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err),"invalid operands to bitwise ^ (float/double)\n"); }
                char* ct1 = (char*)malloc(sizeof(char));strcpy(ct1,"");
                char* ct2 = (char*)malloc(sizeof(char));strcpy(ct2,"");
                checkType($1,$3,ct1,ct2,$$->type);
                if(strcmp(ct1,"")){strcpy($1->str,ct1);}
                if(strcmp(ct2,"")){strcpy($3->str,ct2);}
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s ^ %s\n",code,t,$1->str,$3->str); code++;
            }
            $$->lv=0;
        }
    }
    | EXPR LSHIFT EXPR {
        if (!e){ 
            $$ = createExpr();
            if (tryConstantFold($1, $3, 'l', $$)) { $$->lv = 0; } else {
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err),"invalid operands to << (float/double)\n"); }
                strcpy($$->type,$1->type);
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s << %s\n",code,t,$1->str,$3->str); code++;
            }
            $$->lv=0;
        }
    }
    | EXPR RSHIFT EXPR {
        if (!e){ 
            $$ = createExpr();
            if (tryConstantFold($1, $3, 'r', $$)) { $$->lv = 0; } else {
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err),"invalid operands to >> (float/double)\n"); }
                strcpy($$->type,$1->type);
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s >> %s\n",code,t,$1->str,$3->str); code++;
            }
            $$->lv=0;
        }
    }
    | BNOT EXPR {
    if (!e){
        if (isFloatingType($2->type)){ e=1; sprintf(err+strlen(err),"invalid operand to bitwise ~ (float/double)\n"); }
        $$ = createExpr();
        strcpy($$->type,$2->type);
        if (isNumericConstant($2->str)) {
            int val = (int)atof($2->str);
            sprintf($$->str, "%d", ~val);
            $$->lv = 0;
        } else {
            char* t = genvar(); strcpy($$->str,t);
            sprintf(imcode[code],"%d %s = ~ %s\n",code,t,$2->str); code++;
            $$->lv=0;
        }
    }
}
| BOOLEXPR '?' EXPR ':' EXPR {
   
    if (!e) {
        $$ = createExpr();

        char* cond_var = genvar();
        char* t        = genvar();
        char* res_type = promoteType(getBaseType($3->type), getBaseType($5->type));
        strcpy($$->type, res_type);
        strcpy($$->str, t);
        $$->lv = 0;

        int C0 = code;
        /* C0: true path — cond_var = 1 */
        sprintf(imcode[code], "%d %s = 1\n", code, cond_var); code++;

        /* C1: jump past the false-assign */
        int C1 = code;
        sprintf(imcode[code], "%d goto %d\n", code, code + 2); code++;

        /* C2: false path — cond_var = 0 */
        int C2 = code;
        sprintf(imcode[code], "%d %s = 0\n", code, cond_var); code++;

        /* Backpatch: T list → C0 (true fires → cond=1) */
        backpatch($1->T, C0);
        /* Backpatch: F list → C2 (false fires → cond=0) */
        backpatch($1->F, C2);

        /* C3: branch — if cond == 0 skip true branch */
        int C3 = code;
        int C6 = code + 3;   /* where false-value assignment will be */
        sprintf(imcode[code], "%d if %s == 0 goto %d\n", code, cond_var, C6); code++;

        /* C4: true-branch value */
        sprintf(imcode[code], "%d %s = %s\n", code, t, $3->str); code++;

        /* C5: skip over false branch */
        int C5 = code;
        int C7 = code + 2;   /* end label */
        sprintf(imcode[code], "%d goto %d\n", code, C7); code++;

        /* C6: false-branch value */
        sprintf(imcode[code], "%d %s = %s\n", code, t, $5->str); code++;

        /* C7: execution continues here (code == C7) */
    }
}
 | EXPR '?' EXPR ':' EXPR {
   
    if (!e) {
        $$ = createExpr();

        char* t = genvar();
        char* res_type = promoteType(getBaseType($3->type), getBaseType($5->type));
        strcpy($$->type, res_type);
        strcpy($$->str, t);
        $$->lv = 0;

        int C3 = code + 3;
        int C4 = code + 4;

        sprintf(imcode[code], "%d if %s == 0 goto %d\n", code, $1->str, C3); code++;
        sprintf(imcode[code], "%d %s = %s\n", code, t, $3->str);             code++;
        sprintf(imcode[code], "%d goto %d\n", code, C4);                     code++;
        sprintf(imcode[code], "%d %s = %s\n", code, t, $5->str);             code++;
        /* code == C4 now */
    }
}  
    | FUNCALL {$$ = $1;}
    /* ─────────────────────────────────────────────────────────────
       HEAP ALLOCATION EXPRESSIONS
       Lexer note: TYPE tokens carry their @-prefixed string, e.g.
         @int → str="@int",  @float → str="@float", etc.
       sizeofType() maps "@T" → byte-width (matches lexer semantics).
       All results are typed as ptr:void (raw heap pointer).
       ───────────────────────────────────────────────────────────── */

    /* ── null literal ── */
    | NULLPTR {
        if (!e) {
            $$ = createExpr();
            strcpy($$->str, "0");
            strcpy($$->type, "ptr:void");
            $$->lv = 0;
        }
    }

    /* ── alloc(N) — raw byte allocation ── */
    | ALLOC '(' EXPR ')' {
        if (!e) {
            $$ = createExpr();
            char* t = genvar();
            /* alloc(N) allocates N raw bytes: ALLOC 1 * N */
            sprintf(imcode[code], "%d %s = ALLOC 1 * %s\n", code, t, $3->str);
            code++;
            strcpy($$->str, t);
            strcpy($$->type, "ptr:void");
            $$->lv = 0;
        }
    }

    /* ── alloc(N, @T) — typed allocation ── */
    | ALLOC '(' EXPR ',' TYPE ')' {
        if (!e) {
            $$ = createExpr();
            /* Resolve sizeof(@T) from the TYPE token string */
            int tsz = 4; /* default */
            char* ts = $5->str;
            if (strcmp(ts,"@char")==0||strcmp(ts,"@void")==0)          tsz=1;
            else if (strcmp(ts,"@short")==0)                           tsz=2;
            else if (strcmp(ts,"@int")==0||strcmp(ts,"@float")==0)     tsz=4;
            else if (strcmp(ts,"@long")==0||strcmp(ts,"@double")==0)   tsz=8;
            else if (strcmp(ts,"@ptr")==0||strncmp(ts,"ptr:",4)==0)    tsz=8;
            char* t = genvar();
            /* ALLOC sizeof(@T) * N */
            sprintf(imcode[code], "%d %s = ALLOC %d * %s\n", code, t, tsz, $3->str);
            code++;
            strcpy($$->str, t);
            /* derive typed pointer from the element type */
            char elem[100];
            if (ts[0]=='@') strcpy(elem, ts+1); else strcpy(elem, ts);
            sprintf($$->type, "ptr:%s", elem);
            $$->lv = 0;
        }
    }

    /* ── calloc(N, M) — N elements of M bytes each, zero-initialised ── */
    | CALLOC '(' EXPR ',' EXPR ')' {
        if (!e) {
            $$ = createExpr();
            char* t = genvar();
            sprintf(imcode[code], "%d %s = CALLOC %s, %s\n", code, t, $3->str, $5->str);
            code++;
            strcpy($$->str, t);
            strcpy($$->type, "ptr:void");
            $$->lv = 0;
        }
    }

    /* ── calloc(N, @T) — N typed elements, zero-initialised ── */
    | CALLOC '(' EXPR ',' TYPE ')' {
        if (!e) {
            $$ = createExpr();
            int tsz = 4;
            char* ts = $5->str;
            if (strcmp(ts,"@char")==0||strcmp(ts,"@void")==0)          tsz=1;
            else if (strcmp(ts,"@short")==0)                           tsz=2;
            else if (strcmp(ts,"@int")==0||strcmp(ts,"@float")==0)     tsz=4;
            else if (strcmp(ts,"@long")==0||strcmp(ts,"@double")==0)   tsz=8;
            else if (strcmp(ts,"@ptr")==0||strncmp(ts,"ptr:",4)==0)    tsz=8;
            char* t = genvar();
            sprintf(imcode[code], "%d %s = CALLOC %s, %d\n", code, t, $3->str, tsz);
            code++;
            strcpy($$->str, t);
            char elem[100];
            if (ts[0]=='@') strcpy(elem, ts+1); else strcpy(elem, ts);
            sprintf($$->type, "ptr:%s", elem);
            $$->lv = 0;
        }
    }

    /* ── realloc(p, N) — resize pointer to N bytes ── */
    | REALLOC '(' EXPR ',' EXPR ')' {
        if (!e) {
            $$ = createExpr();
            if (!isPointerType($3->type) &&
                strcmp($3->str,"0")!=0 && strcmp($3->str,"0.0")!=0) {
                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: realloc() first argument must be a pointer, got '%s'\n",
                    yylineno, $3->type);
            }
            char* t = genvar();
            sprintf(imcode[code], "%d %s = REALLOC %s, %s\n", code, t, $3->str, $5->str);
            code++;
            strcpy($$->str, t);
            /* preserve original pointer type if known, else ptr:void */
            if (isPointerType($3->type)) strcpy($$->type, $3->type);
            else strcpy($$->type, "ptr:void");
            $$->lv = 0;
        }
    }
    | TERM {$$ = $1;}
    /* ── pointer operations ── */
    | ADDROF IDEN {
        /* ref x  →  address of x  (produces a ptr:T value) */
        if (!e) {
            $$ = createExpr();
            Symbol* sym = env_get(top, $2);
            if (!sym) {
                e = 1;
                sprintf(err+strlen(err), "Line %d: '%s' not declared in scope\n", yylineno, $2);
                strcpy($$->str, "0");
                strcpy($$->type, "ptr:int");
            } else {
                /* TAC: t = ref x  (address-of) */
                char* t = genvar();
                sprintf(imcode[code], "%d %s = ref %s\n", code, t, $2);
                code++;
                strcpy($$->str, t);
                /* derive pointer type from pointee */
                char base[100];
                extract_base(sym->type, base);
                sprintf($$->type, "ptr:%s", base);
            }
            $$->lv = 0;
        }
    }
    | DEREF IDEN {
        if (!e) {
            $$ = createExpr();
            Symbol* sym = env_get(top, $2);
            if (!sym) {
                e = 1;
                sprintf(err+strlen(err), "Line %d: '%s' not declared in scope\n", yylineno, $2);
                strcpy($$->str, "0");
                strcpy($$->type, "int");
            } else if (strncmp(sym->type, "ptr:", 4) != 0) {
                e = 1;
                sprintf(err+strlen(err), "Line %d: '%s' is not a pointer type (got '%s')\n",
                        yylineno, $2, sym->type);
                strcpy($$->str, "0");
                strcpy($$->type, "int");
            } else {
                int _null_deref = 0;
                for (int _i = code - 1; _i >= 0 && _i >= code - 20; _i--) {
                    if (strstr(imcode[_i], "// DEAD") != NULL) continue;
                    char _lhs[200], _rhs[200]; int _ln;
                    if (sscanf(imcode[_i], "%d %199s = %199[^\n]", &_ln, _lhs, _rhs) == 3) {
                        if (strcmp(_lhs, $2) == 0) {
                            char* _end = _rhs + strlen(_rhs) - 1;
                            while (_end > _rhs && (*_end == ' ' || *_end == '\n')) *_end-- = '\0';
                            if (strcmp(_rhs, "0") == 0 || strcmp(_rhs, "0.0") == 0) {
                                e = 1;
                                _null_deref = 1;
                                sprintf(err+strlen(err),
                                    "Line %d: Error: dereferencing '%s' which is null — guaranteed crash\n",
                                    yylineno, $2);
                            }
                            break;
                        }
                    }
                }
                if (_null_deref) {
                    strcpy($$->str, "0");
                    strcpy($$->type, "int");
                    $$->lv = 1;
                } else {
                    char* t = genvar();
                    sprintf(imcode[code], "%d %s = deref %s\n", code, t, $2);
                    code++;
                    strcpy($$->str, t);
                    strcpy($$->type, sym->type + 4);
                    $$->is_deref = 1;
                    strcpy($$->deref_src, $2);
                    $$->lv = 1;
                }
            }
        }
    }
    ;

FUNCALL: CALL IDEN '(' ARGLIST ')' {
            /* Always initialise $$ to avoid UB when e is already set */
            $$ = createExpr();
            if(!e){
                Function* f = findFunction($2);
                if(f == NULL){
                    e=1;
                    sprintf(err+strlen(err),"Function %s not declared\n",$2);
                } else {
                    int arg_count = 0;
                    struct Expr* arg = $4;
                    Param* param = f->params;

                    /* argument type checking */
                    while(arg && param){
                        arg_count++;
                        if(!isTypeCompatible(param->type, arg->type)){
                            sprintf(err+strlen(err),"Warning: Argument %d type mismatch in call to %s: expected %s, got %s\n",
                                    arg_count, $2, param->type, arg->type);
                        }
                        arg = arg->next;
                        param = param->next;
                    }
                    /* count any extra args beyond what params expects */
                    while(arg){ arg_count++; arg = arg->next; }

                    if(arg_count != f->param_count){
                        e=1;
                        sprintf(err+strlen(err),"Function %s expects %d arguments, got %d\n",
                                $2, f->param_count, arg_count);
                        strcpy($$->type, f->return_type);
                        /* Do NOT fall through into code-gen — bail out now */
                        goto funcall_arglist_done;
                    }

                    {
                    struct Expr* reversed = NULL;
                    arg = $4;
                    Param* rparam = f->params;
                    /* Build cast list in forward order */
                    struct Expr* cast_args = NULL;
                    struct Expr* cast_tail = NULL;
                    int rarg_idx = 1;
                    while(arg && rparam){
                        char* arg_base   = getBaseType(arg->type);
                        char* param_base = getBaseType(rparam->type);
                        struct Expr* ca = createExpr();
                        strcpy(ca->str, arg->str);
                        strcpy(ca->type, arg->type);
                        ca->lv = arg->lv;
                        /* Pass-by-reference: arg->str starts with '&' — skip cast */
                        int is_ref = (arg->str[0] == '&');
                        /* Insert implicit cast if types differ (value args only) */
                        if(!is_ref &&
                           strcmp(arg_base, param_base) != 0 &&
                           getTypeRank(arg_base) > 0 && getTypeRank(param_base) > 0){
                            if(getTypeRank(arg_base) > getTypeRank(param_base)){
                                sprintf(err+strlen(err),
                                    "Warning: Narrowing conversion from %s to %s for argument %d in call to '%s'\n",
                                    arg_base, param_base, rarg_idx, $2);
                            }
                            if(isFloatingType(arg_base) && isIntegerType(param_base)){
                                sprintf(err+strlen(err),
                                    "Warning: Conversion from %s to %s for argument %d in call to '%s' will discard fractional part\n",
                                    arg_base, param_base, rarg_idx, $2);
                            }
                            if(isLiteral(arg->str)){
                                sprintf(ca->str, "(%s)%s", param_base, arg->str);
                            } else {
                                char* tmp = genvar();
                                sprintf(imcode[code], "%d %s = (%s) %s\n", code, tmp, param_base, arg->str);
                                code++;
                                strcpy(ca->str, tmp);
                            }
                            strcpy(ca->type, rparam->type);
                        }
                        ca->next = NULL;
                        if(!cast_args){ cast_args = ca; cast_tail = ca; }
                        else { cast_tail->next = ca; cast_tail = ca; }
                        arg = arg->next;
                        rparam = rparam->next;
                        rarg_idx++;
                    }
                    /* Reverse the cast list for PushParam order */
                    reversed = NULL;
                    arg = cast_args;
                    while(arg){
                        struct Expr* temp = createExpr();
                        strcpy(temp->str, arg->str);
                        strcpy(temp->type, arg->type);
                        temp->lv = arg->lv;
                        temp->next = reversed;
                        reversed = temp;
                        arg = arg->next;
                    }
                    arg = reversed;
                    while(arg){
                        sprintf(imcode[code], "%d PushParam %s\n", code, arg->str);
                        code++;
                        arg = arg->next;
                    }

                    strcpy($$->type, f->return_type);
                    $$->lv = 0;
                    if(strcmp(f->return_type, "void") == 0) {
                        e = 1;
                        sprintf(err+strlen(err), "Cannot use return value of void function '%s'\n", $2);
                        sprintf(imcode[code], "%d Call %s\n", code, $2);
                        code++;
                        strcpy($$->str, "__void__");
                    } else {
                        char* ret_var = genvar();
                        sprintf(imcode[code], "%d %s = Call %s\n", code, ret_var, $2);
                        code++;
                        strcpy($$->str, ret_var);
                    }
                    } /* end inner block */
                    funcall_arglist_done:;
                }
            }
        }
| CALL IDEN '(' ')' {
                $$ = createExpr();

            if(!e){
                Function* f = findFunction($2);
                if(f == NULL){
                    e=1;
                    sprintf(err+strlen(err),"Function %s not declared\n",$2);
                } else {
                    if(f->param_count != 0){
                        e=1;
                        sprintf(err+strlen(err),"Function %s expects %d arguments, got 0\n",
                                $2, f->param_count);
                    }

                    strcpy($$->type, f->return_type);
                    $$->lv = 0;
                    if(strcmp(f->return_type, "void") == 0) {
                        e = 1;
                        sprintf(err+strlen(err), "Cannot use return value of void function '%s'\n", $2);
                        sprintf(imcode[code], "%d Call %s\n", code, $2);
                        code++;
                        strcpy($$->str, "__void__");
                    } else {
                        char* ret_var = genvar();
                        sprintf(imcode[code], "%d %s = Call %s\n", code, ret_var, $2);
                        code++;
                        strcpy($$->str, ret_var);
                    }

                }
            }
        };


ARGLIST: EXPR ',' ARGLIST {
            if(!e){ $$ = $1; $$->next = $3; }
        }
        | EXPR {
            if(!e){ $$ = $1; $$->next = NULL; }
        }
        | '&' EXPR ',' ARGLIST {
            if(!e){
                if(!$2->lv){
                    e=1;
                    sprintf(err+strlen(err), "Pass-by-reference requires a variable (lvalue), not an expression\n");
                    $$ = $2;
                } else {
                    $$ = createExpr();
                    sprintf($$->str, "&%s", $2->str);
                    strcpy($$->type, $2->type);
                    $$->lv = 0;
                    $$->next = $4;
                }
            }
        }
        | '&' EXPR {
            if(!e){
                if(!$2->lv){
                    e=1;
                    sprintf(err+strlen(err), "Pass-by-reference requires a variable (lvalue), not an expression\n");
                    $$ = $2;
                } else {
                    $$ = createExpr();
                    sprintf($$->str, "&%s", $2->str);
                    strcpy($$->type, $2->type);
                    $$->lv = 0;
                    $$->next = NULL;
                }
            }
        };


OP: '+' | '-' | '*' | '/' | '%'| BAND | BOR | BXOR | LSHIFT | RSHIFT;
SUBSCRIPTS: '[' EXPR ']' {
                $$ = createSubscript();
                if (!e) {
                        sprintf($$->indices, "[%s]", $2->str);
                        $$->count = 1;
                } else {
                        strcpy($$->indices, "[0]");
                        $$->count = 1;
                }
        }
        | SUBSCRIPTS '[' EXPR ']' {
                $$ = createSubscript();
                if (!e && $1) {
                        sprintf($$->indices, "%s[%s]", $1->indices, $3->str);
                        $$->count = $1->count + 1;
                } else {
                        strcpy($$->indices, "[0]");
                        $$->count = 1;
                }
        };

TERM: STRING {
    $$ = createExpr();
    strcpy($$->str, $1);
    strcpy($$->type, "char*");
    $$->str_len = strlen($1) - 2 + 1;
    $$->lv = 0;
}
| '(' TYPE ')' EXPR {
    if(!e){
        $$ = createExpr();
        char clean_type[100]; strcpy(clean_type, $2->str);
        if (clean_type[0] == '@') memmove(clean_type, clean_type+1, strlen(clean_type));
        if (isNumericConstant($4->str)) {
            double val = atof($4->str);
            if (strcmp(clean_type,"int")==0||strcmp(clean_type,"short")==0||
                strcmp(clean_type,"long")==0||strcmp(clean_type,"char")==0)
                sprintf($$->str, "%d", (int)val);
            else if (strcmp(clean_type,"float")==0||strcmp(clean_type,"double")==0)
                sprintf($$->str, "%g", val);
            else sprintf($$->str,"(%s)%s",clean_type,$4->str);
            strcpy($$->type, clean_type);
            $$->lv = 0;
        } else {
            sprintf($$->str, "(%s)%s", clean_type, $4->str);
            strcpy($$->type, clean_type);
            $$->lv = 0;
        }
    }
}
| UN OPR IDEN B {
    $$ = createExpr();  
    if (strcmp($1,"-")){
        Env* temp = top; int found=0;
        while(temp){
            if (get(temp->table,$3)){
                found = 1;
                Symbol* t = get(temp->table,$3);
                /*  const check on pre-inc/dec */
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err),"Cannot modify const variable %s\n",$3); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err),"%s is not declared in scope\n",$3); e=1; }
        char*t2=genvar();
        sprintf(imcode[code],"%d %s = %s %c 1\n",code,t2,$3,$2[0]);code++;
        sprintf(imcode[code],"%d %s = %s\n",code,$3,t2);code++;
        strcpy($$->str,t2);
    } else {
        if (!strcmp($2,"--")){e=1;strcpy(err,"--- not allowed");}
        Env* temp = top; int found=0;
        while(temp){
            if (get(temp->table,$3)){
                found = 1;
                Symbol* t = get(temp->table,$3);
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err),"Cannot modify const variable %s\n",$3); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err),"%s is not declared in scope\n",$3); e=1; }
        else {
            char*t=genvar();char*t2=genvar();
            sprintf(imcode[code],"%d %s = %s %c 1\n",code,t,$3,$2[0]);code++;
            sprintf(imcode[code],"%d %s = %s\n",code,$3,t);code++;
            sprintf(imcode[code],"%d %s = - %s\n",code,t2,t);code++;
            strcpy($$->str,t2);
        }
    }
    $$->lv = 0;
}
| UN IDEN OPR B {
    $$ = createExpr();  
    if (strcmp($1,"-")){
        char*t = genvar();char*t2=genvar();
        sprintf(imcode[code],"%d %s = %s\n",code,t,$2);code++;
        sprintf(imcode[code],"%d %s = %s %c 1\n",code,t2,$2,$3[0]);code++;
        sprintf(imcode[code],"%d %s = %s\n",code,$2,t2);code++;
        strcpy($$->str,t);
        Env* temp = top; int found=0;
        while(temp){
            if (get(temp->table,$2)){
                found = 1;
                Symbol* t = get(temp->table,$2);
                /*  const check on post-inc/dec */
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err),"Cannot modify const variable %s\n",$2); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err),"%s is not declared in scope\n",$2); e=1; }
    } else {
        char* t = genvar();char* t1 = genvar();char *t3 = genvar();
        sprintf(imcode[code],"%d %s = %s\n",code,t,$2);code++;
        sprintf(imcode[code],"%d %s = %s %c 1\n",code,t1,$2,$3[0]);code++;
        sprintf(imcode[code],"%d %s = %s\n",code,$2,t1);code++;
        sprintf(imcode[code],"%d %s = -%s\n",code,t3,t);code++;
        strcpy($$->str,t3);
        Env* temp = top; int found=0;
        while(temp){
            if (get(temp->table,$2)){
                found = 1;
                Symbol* t = get(temp->table,$2);
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err),"Cannot modify const variable %s\n",$2); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err),"%s is not declared in scope\n",$2); e=1; }
    }
    $$->lv=0;
}
| UN NUM C {
    $$ = createExpr();  
    if (!strcmp($1,"-")) {
        char negated[100]; sprintf(negated, "-%s", $2);
        strcpy($$->str, negated);
    } else {
        strcpy($$->str, $2);
    }
    if (checkfloat($2)) strcpy($$->type,"float");
    else strcpy($$->type,"int");
    $$->lv = 0;
}
| UN IDEN SUBSCRIPTS {
    $$ = createExpr();  
    Env* temp = top; int found=0; Symbol* sym_found = NULL;
    while(temp){
        if (get(temp->table,$2)){
            found = 1;
            sym_found = get(temp->table,$2);
            strcpy($$->type, sym_found->type);
            break;
        }
        temp = temp->prev;
    }
    if (!found){ sprintf(err+strlen(err),"%s is not declared in scope\n",$2); e=1; }
    if (sym_found) {
        char* base_type = getBaseType(sym_found->type);
        strcpy($$->type, base_type);
    }
    if (sym_found && sym_found->dim_count > 0) {
        char* offset_var = calculateArrayOffset(sym_found, $3, $2);
        if (!strcmp($1,"-")) {
            char* t = genvar(); strcpy($$->str, t);
            sprintf(imcode[code],"%d %s = - %s[%s]\n", code, t, $2, offset_var); code++;
            $$->lv=0;
        } else {
            sprintf($$->str, "%s[%s]", $2, offset_var);
            $$->lv=1;
        }
    } else {
        if (!strcmp($1,"-")) {
            char* t = genvar(); strcpy($$->str, t);
            sprintf(imcode[code],"%d %s = - %s%s\n",code,t,$2,$3->indices); code++;
            $$->lv=0;
        } else {
            sprintf($$->str, "%s%s", $2, $3->indices);
            $$->lv=1;
        }
    }
}
| UN IDEN C {
    $$ = createExpr();  
    if (!strcmp($1,"-")) {
        char* t = genvar(); strcpy($$->str,t);
        sprintf(imcode[code],"%d %s = - %s\n",code,t,$2); code++;
        $$->lv=0;
    } else {
        strcpy($$->str,$2);
        $$->lv=1;
    }
    Env* temp = top; int found=0;
    while(temp){
        if (get(temp->table,$2)){
            found = 1;
            Symbol* t = get(temp->table,$2);
            strcpy($$->type,t->type);
            break;
        }
        temp = temp->prev;
    }
    if (!found){ sprintf(err+strlen(err),"%s is not declared in scope\n",$2); e=1; }
}
| UN CHARR C {
    $$ = createExpr();
    if (!strcmp($1,"-")) {
        char* t = genvar(); strcpy($$->str, t);
        sprintf(imcode[code], "%d %s = - %s\n", code, t, $2); code++;
        $$->lv = 0;
    } else {
        strcpy($$->str, $2);
        $$->lv = 0;
    }
    strcpy($$->type, "char");
}
| UN INC NUM {e=1;strcpy(err,"cannot increment a constant value");}
| UN DEC NUM {e=1;strcpy(err,"cannot decrement a constant value");}
| UN NUM INC {e=1;strcpy(err,"cannot increment a constant value");}
| UN NUM DEC {e=1;strcpy(err,"cannot decrement a constant value");}
;

    OPR: INC {strcpy($$,$1);}| DEC {strcpy($$,$1);};

B : OPR {e=1;strcpy(err,"expression is not assignable");}
  | IDEN {e=1;strcpy(err,"missing operator");}
  | NUM {e=1;strcpy(err,"missing operator");}
  |;
C : IDEN {e=1;strcpy(err,"missing operator");}
  | NUM {e=1;strcpy(err,"missing operator");}
  |;
UN : '-' {strcpy($$,"-");}  | '+' {strcpy($$,"+");} | {strcpy($$,"");} ;
%%

char* genvar(){
    char *re = (char*)malloc(sizeof(char)*100);
    sprintf(re,"t%d",label);
    label++;
    return re;
}

int yyerror(char* msg){ return 0; }

void printQuadruples() {
    FILE *f = fopen("quadruples.txt", "w");
    if (!f) {
        fprintf(stderr, "Error: could not open quadruples.txt for writing\n");
        return;
    }

    fprintf(f, "\n");
    fprintf(f, "================================================================================\n");
    fprintf(f, "                              QUADRUPLES TABLE                                  \n");
    fprintf(f, "================================================================================\n");
    fprintf(f, "  %-4s  %-18s  %-18s  %-18s  %-18s\n",
           "#", "op", "arg1", "arg2", "result");
    fprintf(f, "  %-4s  %-18s  %-18s  %-18s  %-18s\n",
           "----", "------------------", "------------------",
           "------------------", "------------------");

    int q = 0;
    for (int i = 0; i < code; i++) {
        if (imcode[i][0] == '\0') continue;

        char line[10000];
        strcpy(line, imcode[i]);

        int len = strlen(line);
        if (len > 0 && line[len-1] == '\n') line[--len] = '\0';

        char *p = line;
        while (*p == ' ') p++;
        while (*p && (*p >= '0' && *p <= '9')) p++;
        while (*p == ' ') p++;

        char op[100]="", arg1[200]="", arg2[200]="", result[200]="-";
        strcpy(arg2, "-");
        strcpy(result, "-");

        if (strncmp(p, "//", 2) == 0) {
            strcpy(op, p);
            strcpy(arg1, "-");
        }
        else if (strncmp(p, "BeginFunc", 9) == 0) {
            char name[100]; int n;
            sscanf(p, "BeginFunc %s %d", name, &n);
            strcpy(op, "BeginFunc");
            strcpy(arg1, name);
            sprintf(arg2, "%d params", n);
        }
        else if (strncmp(p, "EndFunc", 7) == 0) {
            char name[100]; sscanf(p, "EndFunc %s", name);
            strcpy(op, "EndFunc");
            strcpy(arg1, name);
        }
        else if (strncmp(p, "PopParam", 8) == 0) {
            sscanf(p, "PopParam %s", arg1);
            strcpy(op, "PopParam");
        }
        else if (strncmp(p, "PushParam", 9) == 0) {
            sscanf(p, "PushParam %s", arg1);
            strcpy(op, "PushParam");
        }
        else if (strncmp(p, "Return", 6) == 0) {
            strcpy(op, "Return");
            char val[200]="";
            sscanf(p, "Return %s", val);
            if (val[0]) strcpy(arg1, val);
        }
        else if (strncmp(p, "goto", 4) == 0 &&
                 (p[4]==' '||p[4]=='\0') &&
                 (strstr(p,"if ")==NULL || strstr(p,"if ")>p+4)) {
            char lbl[50]; sscanf(p, "goto %s", lbl);
            strcpy(op, "goto");
            strcpy(arg1, lbl);
        }
        else if (strncmp(p, "if ", 3) == 0) {
            char a1[200], rel[20], a2[200], lbl[50];
            if (sscanf(p, "if %s %s %s goto %s", a1, rel, a2, lbl) == 4) {
                sprintf(op, "if %s", rel);
                strcpy(arg1, a1);
                strcpy(arg2, a2);
                strcpy(result, lbl);
            } else {
                strcpy(op, p);
            }
        }
        else if (strncmp(p, "print", 5) == 0) {
            char val[200];
            sscanf(p, "%*s %s", val);
            strcpy(op, "print");
            strcpy(arg1, val);
        }
        else if (strncmp(p, "input", 5) == 0) {
            char val[200];
            sscanf(p, "%*s %s", val);
            strcpy(op, "input");
            strcpy(arg1, val);
        }
        else if (strncmp(p, "Call ", 5) == 0) {
            char fname[100]; sscanf(p, "Call %s", fname);
            strcpy(op, "Call");
            strcpy(arg1, fname);
        }
        else {
            char *eq = strchr(p, '=');
            if (eq) {
                char lhs[200]; int llen = (int)(eq - p);
                strncpy(lhs, p, llen); lhs[llen] = '\0';
                int ll = strlen(lhs);
                while (ll > 0 && lhs[ll-1] == ' ') lhs[--ll] = '\0';
                strcpy(result, lhs);

                char *rhs = eq + 1;
                while (*rhs == ' ') rhs++;

                if (strncmp(rhs, "Call ", 5) == 0) {
                    char fname[100]; sscanf(rhs, "Call %s", fname);
                    strcpy(op, "Call");
                    strcpy(arg1, fname);
                }
                else if ((rhs[0]=='~'||rhs[0]=='-') && rhs[1]==' ') {
                    op[0] = rhs[0]; op[1] = '\0';
                    strcpy(arg1, rhs+2);
                }
                else if (rhs[0] == '(') {
                    char *cp = strchr(rhs, ')');
                    if (cp) {
                        int tl = (int)(cp - rhs) + 1;
                        strncpy(op, rhs, tl); op[tl] = '\0';
                        strcpy(arg1, cp+1);
                        while (arg1[0]==' ') memmove(arg1,arg1+1,strlen(arg1));
                    } else {
                        strcpy(op, "=");
                        strcpy(arg1, rhs);
                    }
                }
                else {
                    char a1[200], oper[20], a2[200];
                    int parsed = sscanf(rhs, "%s %s %s", a1, oper, a2);
                    if (parsed == 3 && strlen(oper) <= 3 &&
                        (strcmp(oper,"+")==0||strcmp(oper,"-")==0||
                         strcmp(oper,"*")==0||strcmp(oper,"/")==0||
                         strcmp(oper,"%")==0||strcmp(oper,"&")==0||
                         strcmp(oper,"|")==0||strcmp(oper,"^")==0||
                         strcmp(oper,"<<")==0||strcmp(oper,">>")==0||
                         strcmp(oper,"&&")==0||strcmp(oper,"||")==0)) {
                        strcpy(op, oper);
                        strcpy(arg1, a1);
                        strcpy(arg2, a2);
                    } else {
                        strcpy(op, "=");
                        strcpy(arg1, rhs);
                        int al = strlen(arg1);
                        while (al > 0 && (arg1[al-1]==' '||arg1[al-1]=='\n')) arg1[--al]='\0';
                    }
                }
            } else {
                strcpy(op, p);
            }
        }

        { int l;
          l=strlen(op);    while(l>0&&(op[l-1]==' '   ||op[l-1]=='\n'))   op[--l]='\0';
          l=strlen(arg1);  while(l>0&&(arg1[l-1]==' ' ||arg1[l-1]=='\n')) arg1[--l]='\0';
          l=strlen(arg2);  while(l>0&&(arg2[l-1]==' ' ||arg2[l-1]=='\n')) arg2[--l]='\0';
          l=strlen(result);while(l>0&&(result[l-1]==' '||result[l-1]=='\n'))result[--l]='\0';
        }

        fprintf(f, "  %-4d  %-18s  %-18s  %-18s  %-18s\n",
               q++, op, arg1, arg2, result);
    }

    fprintf(f, "================================================================================\n");
    fprintf(f, "  Total quadruples: %d\n", q);
    fprintf(f, "================================================================================\n");

    fclose(f);
}



void generateSymbolTableDOT() {
    FILE* dot = fopen("symbol_table.dot", "w");
    fprintf(dot, "digraph SymbolTable {\n");
        fprintf(dot, "  node [shape=record, style=filled, fillcolor=lightblue];\n");
    for (int i = 0; i < env_count; i++) {
        fprintf(dot, "  scope%d [label=\"{Scope %d - %s|", i, i, (i == 0) ? "Global" : "Local");

        Table* table = envs[i]->table;
        int first = 1;
        for (int j = 0; j < table->size; j++) {
            TableEntry* entry = table->buckets[j];
            while (entry) {
                if (!first) fprintf(dot, "|");
                fprintf(dot, "%s : %s - %d", 
                    entry->value->name, 
                    entry->value->type, 
                    entry->value->offset);
                   
                first = 0;
                entry = entry->next;
            }
        }
        fprintf(dot, "}\"];\n");
        
        // Connect to parent scope
        if (envs[i]->prev != NULL) {
            for (int k = 0; k < i; k++) {
                if (envs[k] == envs[i]->prev) {
                    fprintf(dot, "  scope%d -> scope%d;\n", i, k);
                    break;
                }
            }
        }
    }
    
    fprintf(dot, "}\n");
    fclose(dot);
}

void generateTACFlowDOT() {
    FILE* dot = fopen("tac_flow.dot", "w");
    fprintf(dot, "digraph TAC {\n");
    //fprintf(dot, "  node [shape=box];\n");
        fprintf(dot, "  node [shape=box, style=filled, fillcolor=lightblue];\n");

    for (int i = 0; i < code; i++) {
        //if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        // Escape quotes in labels
        char label[10000];
        strcpy(label, imcode[i]);
        char* newline = strchr(label, '\n');
        if (newline) *newline = '\0';
        
        fprintf(dot, "  n%d [label=\"%s\"];\n",  i, label);
        
        //  FIX: Check if this is a conditional jump (has both "if" and "goto")
        int is_conditional = 0;
        if (strstr(imcode[i], "if") != NULL && strstr(imcode[i], "goto") != NULL) {
            char* if_ptr = strstr(imcode[i], "if");
            char* goto_ptr = strstr(imcode[i], "goto");
            if (if_ptr < goto_ptr) {
                is_conditional = 1;
            }
        }
        
        // Draw edges for control flow
        if (is_conditional) {
            //  CONDITIONAL JUMP: Draw both true and false edges
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                // True branch (goto target)
                fprintf(dot, "  n%d -> n%d [label=\"true\", color=green];\n", i, target);
            }
            
            //  FIX: False branch (fall-through to next line)
            if (i + 1 < code) {
                fprintf(dot, "  n%d -> n%d [label=\"false\", color=red];\n", i, i+1);
            }
        }
        else if (strstr(imcode[i], "goto") != NULL) {
            //  UNCONDITIONAL JUMP: Only goto edge, no fall-through
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                fprintf(dot, "  n%d -> n%d [label=\"goto\"];\n", i, target);
            }
        }
        else if (strstr(imcode[i], "Return") == NULL &&
                 strstr(imcode[i], "BeginFunc") == NULL &&
                 strstr(imcode[i], "EndFunc") == NULL) {
            //  SEQUENTIAL FLOW: Normal statement, fall-through to next
            if (i + 1 < code) {
                fprintf(dot, "  n%d -> n%d [style=dashed];\n", i, i+1);
            }
        }
    }
    
    fprintf(dot, "}\n");
    fclose(dot);
}



// Function to identify basic block leaders
void identifyBasicBlocks() {
    int is_leader[10000] = {0};
    
    // Rule 1: First instruction is a leader
    is_leader[0] = 1;
    
    // Rule 2: Any target of a jump is a leader
    // Rule 3: Any instruction immediately following a jump is a leader
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        // Check for goto statements
        if (strstr(imcode[i], "goto") != NULL) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                if (target >= 0 && target < code) {
                    is_leader[target] = 1;  // Target is a leader
                }
            }
            
            // Instruction after goto is a leader
            if (i + 1 < code) {
                is_leader[i + 1] = 1;
            }
        }
        
        // BeginFunc and EndFunc boundaries
        if (strstr(imcode[i], "BeginFunc") != NULL) {
            if (i + 1 < code) is_leader[i + 1] = 1;
        }
        if (strstr(imcode[i], "EndFunc") != NULL) {
            if (i + 1 < code) is_leader[i + 1] = 1;
        }
    }
    
    // Build basic blocks
    int current_start = -1;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        if (is_leader[i]) {
            // End previous block
            if (current_start != -1) {
                BasicBlock* bb = (BasicBlock*)malloc(sizeof(BasicBlock));
                bb->start_line = current_start;
                bb->end_line = i - 1;
                bb->block_id = block_count++;
                bb->next = blocks;
                blocks = bb;
            }
            current_start = i;
        }
    }
    
    // End last block
    if (current_start != -1) {
        BasicBlock* bb = (BasicBlock*)malloc(sizeof(BasicBlock));
        bb->start_line = current_start;
        bb->end_line = code - 1;
        bb->block_id = block_count++;
        bb->next = blocks;
        blocks = bb;
    }
    
}

// Function to find which block a line belongs to
int getBlockForLine(int line) {
    BasicBlock* bb = blocks;
    while (bb) {
        if (line >= bb->start_line && line <= bb->end_line) {
            return bb->block_id;
        }
        bb = bb->next;
    }
    return -1;
}

// Enhanced DOT generation with basic blocks
void generateTACFlowWithBlocks() {
    identifyBasicBlocks();
    
    FILE* dot = fopen("tac_flow_blocks.dot", "w");
    fprintf(dot, "digraph TAC_Blocks {\n");
    fprintf(dot, "  node [shape=record, style=filled, fillcolor=lightblue];\n");
    fprintf(dot, "  rankdir=TB;\n\n");
    
    // Generate one node per basic block
    BasicBlock* bb = blocks;
    while (bb) {
        fprintf(dot, "  bb%d [label=\"{<b>Block %d|", bb->block_id, bb->block_id);
        
        // Add all instructions in this block
        int first = 1;
        for (int i = bb->start_line; i <= bb->end_line && i < code; i++) {
            //if (strstr(imcode[i], "// DEAD") != NULL) continue;
            
            char label[10000];
            strcpy(label, imcode[i]);
            
            // Escape special characters for DOT
            char escaped[10000];
            int j = 0, k = 0;
            while (label[j] != '\0' && label[j] != '\n') {
                if (label[j] == '|' || label[j] == '{' || label[j] == '}' || 
                    label[j] == '<' || label[j] == '>') {
                    escaped[k++] = '\\';
                }
                escaped[k++] = label[j++];
            }
            escaped[k] = '\0';
            
            if (!first) fprintf(dot, "\\l");  // Left-aligned line break
            //fprintf(dot, "%d: %s", i, escaped);
            fprintf(dot, "%s", escaped);
            first = 0;
        }
        
        fprintf(dot, "\\l}\"];\n");
        bb = bb->next;
    }
    
    fprintf(dot, "\n  // Control flow edges\n");
    
    // Draw edges between basic blocks
    for (int i = 0; i < code; i++) {
        //if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        int current_block = getBlockForLine(i);
        if (current_block == -1) continue;
        
        // Check if this is the last instruction in its block
        bb = blocks;
        int is_block_end = 0;
        while (bb) {
            if (bb->block_id == current_block && i == bb->end_line) {
                is_block_end = 1;
                break;
            }
            bb = bb->next;
        }
        
        if (!is_block_end) continue;  // Only process block-ending instructions
        
        // Check for conditional jump
        int is_conditional = 0;
        if (strstr(imcode[i], "if") != NULL && strstr(imcode[i], "goto") != NULL) {
            char* if_ptr = strstr(imcode[i], "if");
            char* goto_ptr = strstr(imcode[i], "goto");
            if (if_ptr < goto_ptr) {
                is_conditional = 1;
            }
        }
        
        if (is_conditional) {
            // True branch (goto target)
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                int target_block = getBlockForLine(target);
                if (target_block != -1) {
                    fprintf(dot, "  bb%d -> bb%d [label=\"T\", color=green, penwidth=2];\n", 
                            current_block, target_block);
                }
            }
            
            // False branch (fall-through)
            if (i + 1 < code) {
                int next_block = getBlockForLine(i + 1);
                if (next_block != -1 && next_block != current_block) {
                    fprintf(dot, "  bb%d -> bb%d [label=\"F\", color=red, penwidth=2];\n", 
                            current_block, next_block);
                }
            }
        }
        else if (strstr(imcode[i], "goto") != NULL) {
            // Unconditional jump
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                int target_block = getBlockForLine(target);
                if (target_block != -1) {
                    fprintf(dot, "  bb%d -> bb%d [label=\"goto\", penwidth=2];\n", 
                            current_block, target_block);
                }
            }
        }
        else if (strstr(imcode[i], "Return") == NULL &&
                 strstr(imcode[i], "EndFunc") == NULL) {
            // Sequential flow
            if (i + 1 < code) {
                int next_block = getBlockForLine(i + 1);
                if (next_block != -1 && next_block != current_block) {
                    fprintf(dot, "  bb%d -> bb%d [style=dashed, color=gray];\n", 
                            current_block, next_block);
                }
            }
        }
    }
    
    fprintf(dot, "}\n");
    fclose(dot);
}

// Add statistics function
void printBasicBlockStats() {
    printf("\n=== Basic Block Statistics ===\n");
    printf("Total blocks: %d\n", block_count);
    
    BasicBlock* bb = blocks;
    while (bb) {
        int inst_count = 0;
        for (int i = bb->start_line; i <= bb->end_line && i < code; i++) {
            if (strstr(imcode[i], "// DEAD") == NULL) {
                inst_count++;
            }
        }
        printf("Block %d: Lines %d-%d (%d instructions)\n", 
               bb->block_id, bb->start_line, bb->end_line, inst_count);
        bb = bb->next;
    }
}

/*
void generateCallGraphDOT() {
    FILE* dot = fopen("call_graph.dot", "w");
    fprintf(dot, "digraph CallGraph {\n");
    fprintf(dot, "  node [shape=record, style=filled];\n");
    fprintf(dot, "  rankdir=TB;\n");
    fprintf(dot, "  concentrate=true;\n\n");
    
    // Track edges with call site information
    typedef struct CallEdge {
        char caller[100];
        char callee[100];
        int line_number;
        int call_count;
        struct CallEdge* next;
    } CallEdge;
    
    CallEdge* edges = NULL;
    char current_func[100] = "";
    
    // Calculate function metrics
    typedef struct FuncMetrics {
        char name[100];
        int tac_lines;
        int start_line;
        int end_line;
        int call_count;  // How many times this function is called
        struct FuncMetrics* next;
    } FuncMetrics;
    
    FuncMetrics* metrics = NULL;
    
    // Scan TAC for function boundaries, calls, and metrics
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        // Track current function and calculate lines
        if (strstr(imcode[i], "BeginFunc") != NULL) {
            int param_count;
            sscanf(imcode[i], "%*d BeginFunc %s %d", current_func, &param_count);
            
            // Create metrics entry
            FuncMetrics* m = malloc(sizeof(FuncMetrics));
            strcpy(m->name, current_func);
            m->start_line = i;
            m->tac_lines = 0;
            m->call_count = 0;
            m->next = metrics;
            metrics = m;
        }
        
        if (strstr(imcode[i], "EndFunc") != NULL && strcmp(current_func, "") != 0) {
            // Update end line and count TAC instructions
            FuncMetrics* m = metrics;
            while (m) {
                if (strcmp(m->name, current_func) == 0) {
                    m->end_line = i;
                    // Count non-dead, non-control instructions
                    for (int j = m->start_line; j <= m->end_line; j++) {
                        if (strstr(imcode[j], "// DEAD") == NULL &&
                            strstr(imcode[j], "BeginFunc") == NULL &&
                            strstr(imcode[j], "EndFunc") == NULL &&
                            strstr(imcode[j], "PopParam") == NULL) {
                            m->tac_lines++;
                        }
                    }
                    break;
                }
                m = m->next;
            }
        }
        
        // Track function calls with line numbers
        if (strstr(imcode[i], "Call") != NULL && strcmp(current_func, "") != 0) {
            char callee[100];
            if (sscanf(imcode[i], "%*d %*s = Call %s", callee) == 1 ||
                sscanf(imcode[i], "%*d Call %s", callee) == 1) {
                
                // Increment callee's call count
                FuncMetrics* m = metrics;
                while (m) {
                    if (strcmp(m->name, callee) == 0) {
                        m->call_count++;
                        break;
                    }
                    m = m->next;
                }
                
                // Check if edge already exists
                CallEdge* check = edges;
                int exists = 0;
                while (check) {
                    if (strcmp(check->caller, current_func) == 0 &&
                        strcmp(check->callee, callee) == 0) {
                        check->call_count++;
                        exists = 1;
                        break;
                    }
                    check = check->next;
                }
                
                if (!exists) {
                    CallEdge* edge = malloc(sizeof(CallEdge));
                    strcpy(edge->caller, current_func);
                    strcpy(edge->callee, callee);
                    edge->line_number = i;
                    edge->call_count = 1;
                    edge->next = edges;
                    edges = edge;
                }
            }
        }
    }
    
    // Helper function to get color based on return type
    const char* getColorForType(const char* type) {
        if (strcmp(type, "void") == 0) return "lightgray";
        if (strcmp(type, "int") == 0) return "lightblue";
        if (strcmp(type, "float") == 0 || strcmp(type, "double") == 0) return "lightyellow";
        if (strcmp(type, "char") == 0) return "lightgreen";
        return "white";
    }
    
    // Draw function nodes with detailed information
    Function* f = func_list;
    while (f) {
        // Find metrics for this function
        FuncMetrics* m = metrics;
        int tac_lines = 0;
        int total_calls = 0;
        while (m) {
            if (strcmp(m->name, f->name) == 0) {
                tac_lines = m->tac_lines;
                total_calls = m->call_count;
                break;
            }
            m = m->next;
        }
        
        // Build parameter string
        char param_str[500] = "";
        if (f->param_count > 0) {
            Param* p = f->params;
            int first = 1;
            while (p) {
                if (!first) strcat(param_str, ", ");
                char temp[100];
                sprintf(temp, "%s %s", p->type, p->name);
                strcat(param_str, temp);
                first = 0;
                p = p->next;
            }
        } else {
            strcpy(param_str, "void");
        }
        
        // Determine complexity badge
        const char* complexity;
        if (tac_lines < 5) complexity = "Simple";
        else if (tac_lines < 20) complexity = "Medium";
        else complexity = "Complex";
        
        // Generate node with all information
        fprintf(dot, "  \"%s\" [fillcolor=\"%s\", label=<\n", 
                f->name, getColorForType(f->return_type));
        fprintf(dot, "    <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n");
        fprintf(dot, "      <TR><TD BGCOLOR=\"navy\"><FONT COLOR=\"white\"><B>%s</B></FONT></TD></TR>\n", 
                f->name);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>Returns:</B> %s</TD></TR>\n", 
                f->return_type);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>Params:</B> %s</TD></TR>\n", 
                param_str);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>TAC Lines:</B> %d (%s)</TD></TR>\n", 
                tac_lines, complexity);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>Called:</B> %d time%s</TD></TR>\n", 
                total_calls, total_calls == 1 ? "" : "s");
        fprintf(dot, "    </TABLE>\n");
        fprintf(dot, "  >];\n\n");
        
        f = f->next;
    }
    
    fprintf(dot, "\n  // Call relationships\n");
    
    // Draw edges with call information
    CallEdge* e = edges;
    while (e) {
        // Determine edge style based on call frequency
        const char* color = "black";
        int penwidth = 1;
        
        if (e->call_count > 5) {
            penwidth = 3;
            color = "red";
        } else if (e->call_count > 2) {
            penwidth = 2;
            color = "orange";
        }
        
        fprintf(dot, "  \"%s\" -> \"%s\" [label=\"%d call%s\\n@line %d\", "
                     "color=\"%s\", penwidth=%d];\n",
                e->caller, e->callee, 
                e->call_count, e->call_count == 1 ? "" : "s",
                e->line_number,
                color, penwidth);
        e = e->next;
    }
    
    // Add legend (FIXED - removed HR tag)
    fprintf(dot, "\n  // Legend\n");
    fprintf(dot, "  legend [shape=none, margin=0, label=<\n");
    fprintf(dot, "    <TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n");
    fprintf(dot, "      <TR><TD COLSPAN=\"2\" BGCOLOR=\"black\"><FONT COLOR=\"white\"><B>Legend</B></FONT></TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightblue\">int</TD><TD>Integer return type</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightyellow\">float/double</TD><TD>Floating-point return</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightgreen\">char</TD><TD>Character return type</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightgray\">void</TD><TD>No return value</TD></TR>\n");
    fprintf(dot, "      <TR><TD COLSPAN=\"2\" BGCOLOR=\"gray\"></TD></TR>\n");  // ← FIXED: Separator row
    fprintf(dot, "      <TR><TD>Black edge</TD><TD>Called 1-2 times</TD></TR>\n");
    fprintf(dot, "      <TR><TD><FONT COLOR=\"orange\">Orange edge</FONT></TD><TD>Called 3-5 times</TD></TR>\n");
    fprintf(dot, "      <TR><TD><FONT COLOR=\"red\">Red edge</FONT></TD><TD>Called 6+ times</TD></TR>\n");
    fprintf(dot, "    </TABLE>\n");
    fprintf(dot, "  >];\n");
    
    fprintf(dot, "}\n");
    fclose(dot);
    
    
    // Print statistics
    printf("\n=== Call Graph Statistics ===\n");
    printf("Total functions: ");
    int func_count = 0;
    f = func_list;
    while (f) { func_count++; f = f->next; }
    printf("%d\n", func_count);
    
    printf("\nMost called functions:\n");
    FuncMetrics* m = metrics;
    while (m) {
        if (m->call_count > 0) {
            printf("  %s: called %d time%s\n", 
                   m->name, m->call_count, m->call_count == 1 ? "" : "s");
        }
        m = m->next;
    }
    
    printf("\nFunction complexity:\n");
    m = metrics;
    while (m) {
        const char* complexity;
        if (m->tac_lines < 5) complexity = "Simple";
        else if (m->tac_lines < 20) complexity = "Medium";
        else complexity = "Complex";
        
        printf("  %s: %d TAC lines (%s)\n", m->name, m->tac_lines, complexity);
        m = m->next;
    }
    printf("=============================\n");
}

*/


void generateCallGraphDOT() {
    FILE* dot = fopen("call_graph.dot", "w");
    fprintf(dot, "digraph CallGraph {\n");
    fprintf(dot, "  node [shape=record, style=filled, fillcolor=lightblue];\n");
    fprintf(dot, "  rankdir=TB;\n");
    fprintf(dot, "  concentrate=true;\n\n");
    
    // Track edges with call site information
    typedef struct CallEdge {
        char caller[100];
        char callee[100];
        int line_number;
        int call_count;
        struct CallEdge* next;
    } CallEdge;
    
    CallEdge* edges = NULL;
    char current_func[100] = "";
    
    // Calculate function metrics
    typedef struct FuncMetrics {
        char name[100];
        int tac_lines;
        int start_line;
        int end_line;
        int call_count;  // How many times this function is called
        struct FuncMetrics* next;
    } FuncMetrics;
    
    FuncMetrics* metrics = NULL;
    
    // Scan TAC for function boundaries, calls, and metrics
    for (int i = 0; i < code; i++) {
        //if (strstr(imcode[i], "// DEAD") != NULL) continue;
        
        // Track current function and calculate lines
        if (strstr(imcode[i], "BeginFunc") != NULL) {
            int param_count;
            sscanf(imcode[i], "%*d BeginFunc %s %d", current_func, &param_count);
            
            // Create metrics entry
            FuncMetrics* m = malloc(sizeof(FuncMetrics));
            strcpy(m->name, current_func);
            m->start_line = i;
            m->tac_lines = 0;
            m->call_count = 0;
            m->next = metrics;
            metrics = m;
        }
        
        if (strstr(imcode[i], "EndFunc") != NULL && strcmp(current_func, "") != 0) {
            // Update end line and count TAC instructions
            FuncMetrics* m = metrics;
            while (m) {
                if (strcmp(m->name, current_func) == 0) {
                    m->end_line = i;
                    // Count non-dead, non-control instructions
                    for (int j = m->start_line; j <= m->end_line; j++) {
                        if (strstr(imcode[j], "// DEAD") == NULL &&
                            strstr(imcode[j], "BeginFunc") == NULL &&
                            strstr(imcode[j], "EndFunc") == NULL &&
                            strstr(imcode[j], "PopParam") == NULL) {
                            m->tac_lines++;
                        }
                    }
                    break;
                }
                m = m->next;
            }
        }
        
        // Track function calls with line numbers
        if (strstr(imcode[i], "Call") != NULL && strcmp(current_func, "") != 0) {
            char callee[100];
            if (sscanf(imcode[i], "%*d %*s = Call %s", callee) == 1 ||
                sscanf(imcode[i], "%*d Call %s", callee) == 1) {
                
                // Increment callee's call count
                FuncMetrics* m = metrics;
                while (m) {
                    if (strcmp(m->name, callee) == 0) {
                        m->call_count++;
                        break;
                    }
                    m = m->next;
                }
                
                // Check if edge already exists
                CallEdge* check = edges;
                int exists = 0;
                while (check) {
                    if (strcmp(check->caller, current_func) == 0 &&
                        strcmp(check->callee, callee) == 0) {
                        check->call_count++;
                        exists = 1;
                        break;
                    }
                    check = check->next;
                }
                
                if (!exists) {
                    CallEdge* edge = malloc(sizeof(CallEdge));
                    strcpy(edge->caller, current_func);
                    strcpy(edge->callee, callee);
                    edge->line_number = i;
                    edge->call_count = 1;
                    edge->next = edges;
                    edges = edge;
                }
            }
        }
    }
    
    //  UPDATED: Helper function to get color based on return type (ALL TYPES)
    const char* getColorForType(const char* type) {
        if (strcmp(type, "void") == 0) return "lightgray";
        if (strcmp(type, "int") == 0) return "lightyellow";
        if (strcmp(type, "short") == 0) return "lightcyan";
        if (strcmp(type, "long") == 0) return "lightskyblue";
        if (strcmp(type, "float") == 0) return "lightyellow";
        if (strcmp(type, "double") == 0) return "wheat";
        if (strcmp(type, "char") == 0) return "lightgreen";
        if (strcmp(type, "bool") == 0) return "lightpink";
        return "white";
    }
    
    // Draw function nodes with detailed information
    Function* f = func_list;
    while (f) {
        // Find metrics for this function
        FuncMetrics* m = metrics;
        int tac_lines = 0;
        int total_calls = 0;
        while (m) {
            if (strcmp(m->name, f->name) == 0) {
                tac_lines = m->tac_lines;
                total_calls = m->call_count;
                break;
            }
            m = m->next;
        }
        
        // Build parameter string
        char param_str[500] = "";
        if (f->param_count > 0) {
            Param* p = f->params;
            int first = 1;
            while (p) {
                if (!first) strcat(param_str, ", ");
                char temp[100];
                sprintf(temp, "%s %s", p->type, p->name);
                strcat(param_str, temp);
                first = 0;
                p = p->next;
            }
        } else {
            strcpy(param_str, "void");
        }
        
        // Determine complexity badge
        const char* complexity;
        if (tac_lines < 5) complexity = "Simple";
        else if (tac_lines < 20) complexity = "Medium";
        else complexity = "Complex";
        
        // Generate node with all information
        fprintf(dot, "  \"%s\" [fillcolor=lightblue, label=<\n", 
                f->name);
        fprintf(dot, "    <TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n");
        fprintf(dot, "      <TR><TD BGCOLOR=\"lightblue\"><FONT COLOR=\"black\"><B>%s</B></FONT></TD></TR>\n", 
                f->name);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>Returns:</B> %s</TD></TR>\n", 
                f->return_type);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>Params:</B> %s</TD></TR>\n", 
                param_str);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>TAC Lines:</B> %d (%s)</TD></TR>\n", 
                tac_lines, complexity);
        fprintf(dot, "      <TR><TD ALIGN=\"LEFT\"><B>Called:</B> %d time%s</TD></TR>\n", 
                total_calls, total_calls == 1 ? "" : "s");
        fprintf(dot, "    </TABLE>\n");
        fprintf(dot, "  >];\n\n");
        
        f = f->next;
    }
    
    fprintf(dot, "\n  // Call relationships\n");
    
    // Draw edges with call information
    CallEdge* e = edges;
    while (e) {
        // Determine edge style based on call frequency
        const char* color = "black";
        int penwidth = 1;
        
        if (e->call_count > 5) {
            penwidth = 3;
            color = "red";
        } else if (e->call_count > 2) {
            penwidth = 2;
            color = "orange";
        }
        
        fprintf(dot, "  \"%s\" -> \"%s\" [label=\"%d call%s\\n@line %d\", "
                     "color=\"%s\", penwidth=%d];\n",
                e->caller, e->callee, 
                e->call_count, e->call_count == 1 ? "" : "s",
                e->line_number,
                color, penwidth);
        e = e->next;
    }
    
    //  UPDATED: Add complete legend with ALL return types
    fprintf(dot, "\n  // Legend\n");
    fprintf(dot, "  legend [shape=none, margin=0, label=<\n");
    fprintf(dot, "    <TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n");
   /* fprintf(dot, "      <TR><TD COLSPAN=\"2\" BGCOLOR=\"black\"><FONT COLOR=\"white\"><B>Return Type Legend</B></FONT></TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightblue\">int</TD><TD>Integer (32-bit)</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightcyan\">short</TD><TD>Short integer (16-bit)</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightskyblue\">long</TD><TD>Long integer (64-bit)</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightyellow\">float</TD><TD>Float (32-bit)</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"wheat\">double</TD><TD>Double (64-bit)</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightgreen\">char</TD><TD>Character (8-bit)</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightpink\">bool</TD><TD>Boolean</TD></TR>\n");
    fprintf(dot, "      <TR><TD BGCOLOR=\"lightgray\">void</TD><TD>No return value</TD></TR>\n");*/
    fprintf(dot, "      <TR><TD>Black edge</TD><TD>Called 1-2 times</TD></TR>\n");
    fprintf(dot, "      <TR><TD><FONT COLOR=\"orange\">Orange edge</FONT></TD><TD>Called 3-5 times</TD></TR>\n");
    fprintf(dot, "      <TR><TD><FONT COLOR=\"red\">Red edge</FONT></TD><TD>Called 6+ times</TD></TR>\n");
    fprintf(dot, "    </TABLE>\n");
    fprintf(dot, "  >];\n");
    
    fprintf(dot, "}\n");
    fclose(dot);
    
    
    // Print statistics
    printf("\n=== Call Graph Statistics ===\n");
    printf("Total functions: ");
    int func_count = 0;
    f = func_list;
    while (f) { func_count++; f = f->next; }
    printf("%d\n", func_count);
    
    printf("\nMost called functions:\n");
    FuncMetrics* m = metrics;
    while (m) {
        if (m->call_count > 0) {
            printf("  %s: called %d time%s\n", 
                   m->name, m->call_count, m->call_count == 1 ? "" : "s");
        }
        m = m->next;
    }
    
    printf("\nFunction complexity:\n");
    m = metrics;
    while (m) {
        const char* complexity;
        if (m->tac_lines < 5) complexity = "Simple";
        else if (m->tac_lines < 20) complexity = "Medium";
        else complexity = "Complex";
        
        printf("  %s: %d TAC lines (%s)\n", m->name, m->tac_lines, complexity);
        m = m->next;
    }
    printf("=============================\n");
}

void generateAllImages() {
    system("dot -Tpng tac_flow.dot -o tac_flow.png 2>/dev/null");
    system("dot -Tpng tac_flow_blocks.dot -o tac_flow_blocks.png 2>/dev/null");
    system("dot -Tpng call_graph.dot -o call_graph.png 2>/dev/null");
    system("dot -Tpng symbol_table.dot -o symbol_table.png 2>/dev/null");
}


int main(int argc, char* argv[]) {
    if (argc < 2) {
        printf("Enter your code \n");
        yyin = stdin;
        memset(imcode, 0, sizeof(imcode));
        yyparse();
    } else {
        FILE* f = fopen(argv[1], "r");
        if (!f) {
            printf("Error: Cannot open file %s\n", argv[1]);
            return 1;
        }

        fseek(f, 0, SEEK_END);
        long fsize = ftell(f);
        fseek(f, 0, SEEK_SET);
        char* raw = (char*)malloc(fsize + 2);
        if (!raw) { fclose(f); return 1; }
        fread(raw, 1, fsize, f);
        raw[fsize] = '\0';
        fclose(f);

        /* Preprocess:
           - strip carriage returns (\r) so Windows files work
           - ensure a space before and after every '$' so "2$" lexes as NUM + '$'
           - ensure file ends with a newline so flex sees a clean EOF */
        char* clean = (char*)malloc(fsize * 3 + 4);
        if (!clean) { free(raw); return 1; }
        int j = 0;
        for (int i = 0; i < (int)fsize; i++) {
            if (raw[i] == '\r') continue;              /* strip \r */
            if (raw[i] == '$') {
                if (j > 0 && clean[j-1] != ' ' && clean[j-1] != '\t' && clean[j-1] != '\n')
                    clean[j++] = ' ';                  /* space before $ */
                clean[j++] = '$';
                clean[j++] = ' ';                      /* space after $ */
            } else {
                clean[j++] = raw[i];
            }
        }
        if (j == 0 || clean[j-1] != '\n') clean[j++] = '\n'; /* trailing newline */
        clean[j] = '\0';
        free(raw);

        memset(imcode, 0, sizeof(imcode));
        yy_scan_string(clean);  /* feed preprocessed source to lexer */
        yyparse();
        free(clean);
    }

    remove("unopt.tac");
    
if (!e) {
    FILE* tac_file = fopen("unopt.tac", "w");
    if (tac_file) {
        for (int i = 0; i < code; i++)
            fprintf(tac_file, "%s", imcode[i]);
        fclose(tac_file);
    }
    //write_symtab_json(); 
    FILE* sym_file = fopen("symboltable.txt", "w");
if (sym_file) {
    print_all_envs(sym_file);
    fclose(sym_file);
}
    //generateInteractiveDashboard();
} else {
    /* Semantic errors occurred — write a sentinel so the pipeline
       knows to stop cleanly instead of assembling stale TAC.      */
    FILE* tac_file = fopen("unopt.tac", "w");
    if (tac_file) {
        fprintf(tac_file, "# SEMANTIC_ERROR\n");
        fclose(tac_file);
    }
}
return e ? 1 : 0;   /* non-zero exit when errors exist */
}