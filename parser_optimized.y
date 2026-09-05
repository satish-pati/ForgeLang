%{
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include<ctype.h>
#include<float.h>
#include<math.h>
extern FILE *yyin;
extern char buffer[];
extern int yylineno;
extern int prev_lineno;
int err_line = 0;  
char err[32768];
int e=0;
int label=0;
char* genvar();
void printQuadruples();
char imcode[10000][10000];
int code=0;
#define FOR_STASH_DEPTH 16
#define FOR_STASH_SLOTS 64
// for_incr_stash[i][j]= j-th increment instruction of i-th loop
static char for_incr_stash[FOR_STASH_DEPTH][FOR_STASH_SLOTS][10000];
// how many increment instructions are used for each loop
static int  for_incr_count[FOR_STASH_DEPTH];
static int is_ref_param(int func_start_idx, const char *varname);
static int  for_incr_sp = 0;  // depth 
// scope env offset
int offset=0; 
int saveoffset;
int string_count = 0; 
int loop_depth = 0;
int switch_depth = 0;
char current_function[100] = "";
char current_return_type[100] = "";
int in_function = 0;
int has_return_statement = 0;
char input_filename[10240] = "";


/* Enum constant storage: name-value, chained by hash collision */
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

/* Store enum constant into hash table */
void enum_put(const char* name, int value) {
    unsigned int idx = enum_hash(name);
    EnumEntry* e2 = malloc(sizeof(EnumEntry));
    strcpy(e2->name, name);
    e2->value = value;
    e2->next = enum_table[idx];
    enum_table[idx] = e2;
}

/* Lookup enum constant value; returns 1 on hit */
int enum_get(const char* name, int* out_value) {
    unsigned int idx = enum_hash(name);
    EnumEntry* e2 = enum_table[idx];
    while (e2) {
        if (strcmp(e2->name, name) == 0) { *out_value = e2->value; return 1; }
        e2 = e2->next;
    }
    return 0;
}
/* Check if an identifier is a declared enum constant */
int is_enum_constant(const char* name) {
    int dummy;
    return enum_get(name, &dummy);
}
int _enum_next_val = 0;  

/* Parameter node: linked list of (name, type, is_ref) for function params */
typedef struct Param{
    char name[100];
    char type[100];
    int  is_ref;   
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

/* Function record: name, return type, param list, param count, entry label */
typedef struct Function{
    char name[100];
    char return_type[100];
    Param* params;
    int param_count;
    int start_label; // label in tac 
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

/* Symbol table entry: name, type, memory offset, array dimensions, decl line */
typedef struct Symbol{
        char name[100];
        char type[100];
        int size;
        int offset;
        int dimensions[10];
        int dim_count;
        int decl_line;   
        struct Symbol*next;
} Symbol;

/* Type wrapper: string repr + byte size */

struct Type{
        char str[1000];
        int size;
};

/* Declaration descriptor: key=varname, type/lt=declared/init type, op=init value */
struct Decl{
        char key[1000];
        char type[1000];
        char lt[100];
        char op[100];
        int size;
        int is_literal;
        int re;
        int str_len; //if string
        struct Decl* next;
};

//a record of an incomplete jump instruction that needs to be fixed later
struct Node{
        struct Node* next;
        int addr;
};

/* Expression result: TAC name (str), type, lv=is lvalue, deref info */
struct Expr{
        char str[1000]; //Generated temp variable ("t1")
        char type[100];
        int lv;
        int str_len;
        int is_deref;   // is dereffered    
        char deref_src[100]; 
        struct Expr* next;
};

/* Backpatch lists: T=true-jumps, F=false-jumps, N=fall-through, B=break, C=continue */
struct BoolNode{
        struct Node* T;
        struct Node* F;
        struct Node* N;
        struct Node* B;
        struct Node* C;
};

/* Array subscript collector: accumulates [i][j]... indices as a string */
struct Subscript{
        char indices[1000];
        int count;
};

struct Node* createNode(int addr){
        struct Node* node = (struct Node*)malloc(sizeof(struct Node));
        node->next = NULL;
        node->addr = addr;// current addr tac line
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

/* Merge two backpatch lists into one */
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

/* Flip a relational operator, e.g. < - >= (used when inverting branch conditions) */
#define FALL_THROUGH (-1)
static const char* negateOp(const char* op) {
    if (strcmp(op,"<")  == 0) return ">=";
    if (strcmp(op,">")  == 0) return "<=";
    if (strcmp(op,"<=") == 0) return ">";
    if (strcmp(op,">=") == 0) return "<";
    if (strcmp(op,"==") == 0) return "!=";
    if (strcmp(op,"!=") == 0) return "==";
    return op;
}

/* Rewrite "if a < b goto L" - "if a >= b goto L" in-place for short-circuit code-gen */
static int flipCondToTrue(int line_idx) {
    char* line = imcode[line_idx];
    char* p = strstr(line, " if ");
    if (!p) return 0;
    int   lnum;
    char  op1[200], rel[10], op2[200];
    if (sscanf(line, "%d if %s %s %s goto", &lnum, op1, rel, op2) != 4)
        return 0;
    const char* orig_rel = negateOp(rel);
    sprintf(line, "%d if %s %s %s goto ", lnum, op1, orig_rel, op2);
    return 1;
}

/* Return 1 if the string contains a dot (i.e. looks like a float literal) */
int checkfloat(char* t){
        while(*t){
                if (*t=='.') return 1;
                t++;
        }
        return 0;
}

/* Fill in all unresolved goto targets in a backpatch list(T,F) with the given address */
void backpatch(struct Node* a,int addr){
        while(a!=NULL){
                if (a->addr == FALL_THROUGH) { a = a->next; continue; }
                int len = strlen(imcode[a->addr]);
                if (imcode[a->addr][len-1] != '\n') { //target address is not yet appended
                    sprintf(imcode[a->addr] + len, "%d\n", addr);
                }
                a = a->next;
        }
}


/* Return 1 if the string is a valid integer or float literal */
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

/* Strip array brackets and "const" prefix to get the raw type name */
char* getBaseType(char* type_str) {
    static char base[100];
    
    char* actual_type = type_str;
    if (strncmp(type_str, "const ", 6) == 0) {
        actual_type = type_str + 6;
    }
    
    char* bracket = strchr(actual_type, '[');
    if (bracket) {
        int len = bracket - actual_type;
        strncpy(base, actual_type, len);
        base[len] = '\0';
        return base;
    }
    return actual_type;
}

/* Numeric rank for implicit-conversion ordering: char=1 … double=6 */
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

/* Return whichever of t1/t2 has the higher rank (usual arithmetic conversions) */
char* promoteType(char* t1, char* t2){
    if (strcmp(t1, t2) == 0) return t1;
    int rank1 = getTypeRank(t1);
    int rank2 = getTypeRank(t2);
    return (rank1 > rank2) ? t1 : t2;
}

int isPointerType(const char* type) {
    if (!type) return 0;
    return (strncmp(type, "ptr:", 4) == 0);
}

char* normalizeType(const char* type, char* out) {
    if (strcmp(type, "char*") == 0) { strcpy(out, "ptr:char"); return out; }
    strncpy(out, type, 99); out[99] = '\0';
    return out;
}

/* Check assignment/return compatibility, emit narrowing warnings */

int isTypeCompatible(char* expected, char* actual) {
    char exp_clean[100], act_clean[100];
    strcpy(exp_clean, expected);
    strcpy(act_clean, actual);
    if(strncmp(exp_clean, "const ", 6) == 0) {
        strcpy(exp_clean, exp_clean + 6);
    }
    if(strncmp(act_clean, "const ", 6) == 0) {
        strcpy(act_clean, act_clean + 6);
    }
    char* exp_base = getBaseType(exp_clean);
    char* act_base = getBaseType(act_clean);
    int exp_is_ptr = (strncmp(exp_base, "ptr:", 4) == 0);
    int act_is_ptr = (strncmp(act_base, "ptr:", 4) == 0);
    if (exp_is_ptr || act_is_ptr) {
        if (!exp_is_ptr || !act_is_ptr) return 0;  
        if (strcmp(exp_base, act_base) != 0) {
    e = 1;   
    sprintf(err+strlen(err),
        "Line %d: Error: pointer type mismatch: "   
        "returning '%s' where '%s' expected\n",
        yylineno, act_base, exp_base);
    return 0; 
}

    }
    if (strcmp(exp_base, act_base) == 0) return 1;
    int exp_rank = getTypeRank(exp_base);
    int act_rank = getTypeRank(act_base);
    if (exp_rank > 0 && act_rank > 0) {
        if (act_rank > exp_rank) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Implicit narrowing conversion from %s to %s\n",
                yylineno, act_base, exp_base);
        }
        if (isFloatingType(act_base) && isIntegerType(exp_base)) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Conversion from %s to %s may lose precision\n",
                yylineno, act_base, exp_base);
        }        
        return 1;  
    }
    return 0;
}

/* Warn if a numeric literal is outside the target type's range */
void validateNumericLiteral(char* literal, char* target_type, char* var_name) {
    if (!isNumericConstant(literal)) return;
    double value = atof(literal);
    if (strcmp(target_type, "char") == 0) {
        if (value < -128 || value > 127)
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %.0f for '%s' exceeds char range [-128, 127]\n",
                yylineno, value, var_name);
    }
    else if (strcmp(target_type, "short") == 0) {
        if (value < -32768 || value > 32767)
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %.0f for '%s' exceeds short range [-32768, 32767]\n",
                yylineno, value, var_name);
    }
    else if (strcmp(target_type, "int") == 0) {
        if (value < -2147483648.0 || value > 2147483647.0)
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %.0f for '%s' exceeds int range [-2147483648, 2147483647]\n",
                yylineno, value, var_name);
    }
    else if (strcmp(target_type, "long") == 0) {
        if (value > 9223372036854775807.0 || value < -9223372036854775808.0)
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %.0f for '%s' exceeds long range\n",
                yylineno, value, var_name);
    }
    else if (strcmp(target_type, "float") == 0) {
        if (value > FLT_MAX || value < -FLT_MAX) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %g for '%s' exceeds float range [-%g, %g] (will be inf)\n",
                yylineno, value, var_name, FLT_MAX, FLT_MAX);
        } else if (value != 0.0 && fabs(value) < FLT_MIN) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %g for '%s' is too small for float (will underflow to 0)\n",
                yylineno, value, var_name);
        }
    }
    else if (strcmp(target_type, "double") == 0) {
        if (isinf(value) || (value > DBL_MAX || value < -DBL_MAX)) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer for '%s' exceeds double range (will be inf)\n",
                yylineno, var_name);
        } else if (value != 0.0 && fabs(value) < DBL_MIN) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Initializer %g for '%s' is too small for double (will underflow to 0)\n",
                yylineno, value, var_name);
        }
    }
}
/* Return 1 if any two params in the list share the same name */

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

static int g_const_fold_arith;

/* Fold op1 OP op2 at parse time if both are constants; returns 1 on success */
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
        sprintf(result->str, "%d", (int)res);
        strcpy(result->type, "int");
    }
    result->lv = 0;
    g_const_fold_arith++;
    return 1;
}


Symbol* createSymbol(char* name){
        Symbol* node = (Symbol*)malloc(sizeof(Symbol));
        memset(node, 0, sizeof(Symbol));
        strcpy(node->name,name);
        node->decl_line = yylineno; 
        return node;
}

/* Scope frame: pointer to parent scope + symbol hash table */

typedef struct Env {
    struct Env* prev;
    int prev_offset;
    struct Table* table;
} Env;

Env* envs[1000];
int env_count = 0;
/* Hash table bucket entry (chained hashing) */

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
/* Insert or overwrite a symbol in the hash table */

void put(Table* table, const char* key, Symbol* sym) {
    unsigned int index = hash(key);
    TableEntry* new_entry = malloc(sizeof(TableEntry));
    new_entry->key = strdup(key);
    new_entry->value = sym;
    new_entry->next = table->buckets[index];
    table->buckets[index] = new_entry;
}
/* Lookup a symbol in the hash table; returns NULL if not found */

Symbol* get(Table* table, const char* key) {
    unsigned int index = hash(key);
    TableEntry* entry = table->buckets[index];
    while (entry) {
        if (strcmp(entry->key, key) == 0) return entry->value;
        entry = entry->next;
    }
    return NULL;
}
/* Push a new scope frame (allocates env + fresh table, saves caller offset) */
Env* create_env(Env* prev,int offset) {
    Env* env = malloc(sizeof(Env));
    env->prev = prev;
    env->table = create_table();
    env->prev_offset = offset;
    envs[env_count++] = env;
    return env;
}

/* Insert symbol into current scope */

void env_put(Env* env, const char* key, Symbol* sym) {
    put(env->table, key, sym);
}

/* Walk scope chain outward until the name is found (lexical scoping) */

Symbol* env_get(Env* env, const char* key) {
    for (Env* e = env; e != NULL; e = e->prev) {
        Symbol* found = get(e->table, key);
        if (found != NULL) return found;
    }
    return NULL;
}

Env* top = NULL;
static int type_byte_size(const char* base) {
    if (strcmp(base,"char"  )==0) return 1;
    if (strcmp(base,"short" )==0) return 2;
    if (strcmp(base,"int"   )==0) return 4;
    if (strcmp(base,"float" )==0) return 4;
    if (strcmp(base,"long"  )==0) return 8;
    if (strcmp(base,"double")==0) return 8;
    if (strncmp(base,"ptr:",4)==0) return 8;  
    return 4; 
}

static void extract_base(const char* full_type, char* out) {
    strcpy(out, full_type);
    char* bracket = strchr(out, '[');
    if (bracket) *bracket = '\0';
    if (out[0] == '@') memmove(out, out+1, strlen(out));
}

#define MAX_SYMS 512
static int collect_symbols(Table* table, Symbol** out) {
    int n = 0;
    for (int i = 0; i < table->size && n < MAX_SYMS; i++) {
        TableEntry* e = table->buckets[i];
        while (e && n < MAX_SYMS) { out[n++] = e->value; e = e->next; }
    }
    for (int i = 1; i < n; i++) {
        Symbol* key = out[i]; int j = i-1;
        while (j >= 0 && out[j]->offset > key->offset) { out[j+1]=out[j]; j--; }
        out[j+1] = key;
    }
    return n;
}

void print_table(Table* table) {
    Symbol* syms[MAX_SYMS];
    int n = collect_symbols(table, syms);
    for (int i = 0; i < n; i++) {
        Symbol* s = syms[i];
        char base[100]; extract_base(s->type, base);
        int elem_size = type_byte_size(base);
        int total_elems = 1;
        for (int d = 0; d < s->dim_count; d++) total_elems *= s->dimensions[d];
        int total_bytes = elem_size * (total_elems > 0 ? total_elems : 1);
        char dim_str[100] = "";
        if (s->dim_count > 0) {
            for (int d = 0; d < s->dim_count; d++) {
                char part[20]; sprintf(part, "[%d]", s->dimensions[d]);
                strcat(dim_str, part);
            }
        } else if (strchr(s->type, '[') != NULL) {
            char* p = strchr(s->type, '[');
            strcpy(dim_str, p ? p : "");
        }
        char category[20];
        if (s->dim_count > 1)       strcpy(category, "multi-dim array");
        else if (s->dim_count == 1) strcpy(category, "array");
        else if (strchr(s->type,'[') != NULL) strcpy(category, "array");
        else                        strcpy(category, "scalar");
        char full_type[100];
        snprintf(full_type, sizeof(full_type), "%s%s", base, dim_str);
        printf("  %-8d  %-20s  %-20s  %-8d  %-8d  %-16s\n",
            s->offset,
            s->name,
            full_type,
            elem_size,
            total_bytes,
            category);
    }
}
void print_all_envs() {
    int non_empty = 0;
    for (int i = 0; i < env_count; i++) {
        for (int b = 0; b < envs[i]->table->size; b++) {
            if (envs[i]->table->buckets[b]) { non_empty++; break; }
        }
    }
    printf("\n");
    printf("==================================================================================\n");
    printf("                        SYMBOL TABLE  (Storage Layout)                      \n");
    printf("==================================================================================\n");
    int scope_printed = 0;
    for (int i = 0; i < env_count; i++) {
        int has_syms = 0;
        for (int b = 0; b < envs[i]->table->size; b++)
            if (envs[i]->table->buckets[b]) { has_syms = 1; break; }
        char scope_label[50];
            printf("\n");
        if (i == 0) strcpy(scope_label, "Global");
        else        sprintf(scope_label, "Local (scope %d)", i);
        printf("  Scope %d  [%s]\n", i, scope_label);
        printf("  %-8s  %-20s  %-20s  %-8s  %-8s  %-16s\n",
               "Offset", "Name", "Type", "ESize", "Total", "Category");
        printf("  %-8s  %-20s  %-20s  %-8s  %-8s  %-16s\n",
               "--------", "--------------------", "--------------------",
               "--------", "--------", "----------------");
        if (!has_syms) {
            printf("  (no symbols)\n");
        } else {
            print_table(envs[i]->table);
        }
        scope_printed++;
    }
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
                printf("\n");
    printf("==================================================================================\n");
    printf("  Total symbols: %d  |  Total storage: %d bytes\n", total_vars, total_bytes);
        printf("==================================================================================\n");
}

typedef struct OptStats {
    int const_fold_arith;
    int const_fold_cond;
    int copy_prop;
    int alg_simp;
    int bool_simp;
    int strength_red;
    int cse;
    int peephole;
    int identity;
    int dead_store;
    int redund_load;
    int dead_code;
    int redund_jump;
    int jump_chain;
    int dead_var;
    int dead_const;
    int dead_branch;
    int dead_hoist;
    int ive;
    int fallthrough_opt;
    int total_optimized;
} OptStats;
//static int g_const_fold_arith = 0;
static int g_const_fold_cond  = 0;
static int g_copy_prop        = 0;
static int g_alg_simp         = 0;
static int g_bool_simp        = 0;
static int g_strength_red     = 0;
static int g_cse              = 0;
static int g_peephole         = 0;
static int g_identity         = 0;
static int g_dead_store       = 0;
static int g_redund_load      = 0;
static int g_dead_code        = 0;
static int g_redund_jump      = 0;
static int g_jump_chain       = 0;
static int g_dead_var         = 0;
static int g_dead_const       = 0;
static int g_dead_branch      = 0;
static int g_dead_hoist       = 0;
static int g_ive              = 0;

static int count_live_lines(void) {
    int n = 0;
    for (int i = 0; i < code; i++) {
        if (imcode[i][0] == '\0') continue;
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        n++;
    }
    return n;
}

static void collect_opt_stats(OptStats *s) {
    memset(s, 0, sizeof(*s));
    s->total_optimized = count_live_lines();
    s->const_fold_arith = g_const_fold_arith;
    s->const_fold_cond  = g_const_fold_cond;
    s->copy_prop        = g_copy_prop;
    s->alg_simp         = g_alg_simp;
    s->bool_simp        = g_bool_simp;
    s->strength_red     = g_strength_red;
    s->cse              = g_cse;
    s->peephole         = g_peephole;
    s->identity         = g_identity;
    s->dead_store       = g_dead_store;
    s->redund_load      = g_redund_load;
    s->dead_code        = g_dead_code;
    s->redund_jump      = g_redund_jump;
    s->jump_chain       = g_jump_chain;
    s->dead_var         = g_dead_var;
    s->dead_const       = g_dead_const;
    s->dead_branch      = g_dead_branch;
    s->dead_hoist       = g_dead_hoist;
    s->ive              = g_ive;
    int total_orig,total_origthis = 0;
    FILE *unopt_f = fopen("unopt.tac", "r");
    if (unopt_f) {
        char buf[16384];
        while (fgets(buf, sizeof(buf), unopt_f)) {
            if (buf[0] != '\0' && buf[0] != '\n') total_orig++;
        }
        fclose(unopt_f);
    } else {
        total_orig = s->total_optimized;
    }
    int total_eliminated = total_orig - s->total_optimized;
    FILE *unoptimzd_f = fopen("unoptimzed.tac", "r");
    if(unoptimzd_f){
        char buf[16384];
        while (fgets(buf, sizeof(buf), unoptimzd_f)) {
            if (buf[0] != '\0' && buf[0] != '\n') total_origthis++;
        }
        total_eliminated=total_orig-total_origthis;
        fclose(unoptimzd_f);
    }
    int accounted_for =
        s->const_fold_arith + s->const_fold_cond + s->copy_prop +
        s->alg_simp + s->bool_simp + s->strength_red + s->cse +
        s->peephole + s->identity + s->dead_store + s->redund_load +
        s->dead_code + s->redund_jump + s->jump_chain + s->dead_var +
        s->dead_const + s->dead_branch + s->dead_hoist + s->ive;
    s->fallthrough_opt = total_eliminated;
}
void generateOptimizationReport(void) {
    OptStats s;
    collect_opt_stats(&s);
    int total_orig = 0;
    FILE *unopt = fopen("unopt.tac", "r");
    if (unopt) {
        char buf[16384];
        while (fgets(buf, sizeof(buf), unopt)) {
            if (buf[0] != '\0' && buf[0] != '\n') total_orig++;
        }
        fclose(unopt);
    } else {
        int total_elim =
            s.dead_code  + s.dead_store + s.dead_var   + s.dead_const +
            s.dead_hoist + s.dead_branch + s.peephole  + s.identity;
        total_orig = s.total_optimized + total_elim;
    }
    int total_elim = total_orig - s.total_optimized;
    double reduction_pct = (total_orig > 0)
        ? (100.0 * total_elim / total_orig) : 0.0;
    FILE *fp = fopen("optimization_report.txt", "w");
    if (!fp) { fprintf(stderr, "[OptReport] Cannot open optimization_report.txt\n"); return; }
    fprintf(fp,
        "========================================================================\n"
        "                     COMPILER OPTIMIZATION REPORT                      \n"
        "========================================================================\n"
        "\n"
        "  TAC instructions before optimisation : %d\n"
        "  TAC instructions after  optimisation : %d\n"
        "  Instructions eliminated              : %d\n"
        "  TAC Code size reduction                  : %.1f%%\n"
        "\n",
        total_orig, s.total_optimized, total_elim, reduction_pct);
    fprintf(fp,
        "========================================================================\n"
        "  PER-PASS BREAKDOWN\n"
        "========================================================================\n"
        "\n"
        "  Pass                          | Instances | Effect\n"
        "  ------------------------------|-----------|----------------------------\n");
#define ROW(name, count, effect) \
    fprintf(fp, "  %-30s| %9d | %s\n", (name), (count), (effect));
    ROW("Fallthrough Optimizations", s.fallthrough_opt, "Eliminates redundant jumps ");
    ROW("Strength Reduction",          s.strength_red,     "x*2^k -> x<<k, x/2^k -> x>>k, x*2 -> x+x");
    ROW("Dead Variable Elimination",   s.dead_var,         "Assignments to never-read variables removed");
    ROW("Induction Variable Elim",     s.ive,              "Loop multiplies replaced by additive updates");
    ROW("Constant Folding (arith)",    s.const_fold_arith, "Arithmetic on literals evaluated at compile time");
    ROW("Loop Invariant Code Motion",  s.dead_hoist,       "Loop-invariant quads hoisted before loop header");
    ROW("Copy Propagation",            s.copy_prop,        "Variable uses replaced by their copied value");
    ROW("Common Subexpr Elim (CSE)",   s.cse,              "Repeated expressions replaced by earlier result");
    ROW("Peephole Optimisation",       s.peephole,         "Adjacent redundant assignments removed");
    ROW("Identity Elimination",        s.identity,         "x = x assignments removed");
    ROW("Dead Store Elimination",      s.dead_store,       "Assignments whose value is overwritten before use");
    ROW("Redundant Load Elimination",  s.redund_load,      "Duplicate loads of the same variable aliased");
    ROW("Dead Code Elimination",       s.dead_code,        "Unreachable instructions after gotos / Returns");
    ROW("Redundant Jump Elimination",  s.redund_jump,      "goto TARGET where TARGET is the next live line");
    ROW("Jump Chaining",               s.jump_chain,       "Chains of gotos collapsed to final target");
    ROW("Algebraic Simplification",    s.alg_simp,         "x*1->x, x+0->x, x-x->0, x/x->1, x^x->0 ...");
    ROW("Boolean Simplification",      s.bool_simp,        "Logical identities: x&&1->x, x||0->x, x==x->1 ...");
    ROW("Dead Constant Elimination",   s.dead_const,       "Constant assignments to never-read variables");
    ROW("Dead Branch Elimination",     s.dead_branch,      "Conditional branches that are always taken");
    ROW("Constant Folding (cond)",     s.const_fold_cond,  "Always-true/false branches folded or removed");
#undef ROW
    fprintf(fp,
        "\n"
        "========================================================================\n"
        "  END OF REPORT\n"
        "========================================================================\n");
    fclose(fp);
}

/* Compute byte offset TAC for an array access; bounds-checks constant indices-Too many subscripts for array */
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
        sprintf(err+strlen(err), "Line %d: Too many subscripts for array %s\n", yylineno, base_name);
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
        if (idx < 0) {
            e = 1;
            sprintf(err+strlen(err), "Line %d: Array index %d is negative for array %s\n", yylineno, idx, base_name);
        } else if (idx >= sym->dimensions[0] && sym->dimensions[0] > 0) {
            e = 1;
            sprintf(err+strlen(err), "Line %d: Array index %d out of bounds for array %s[%d] (valid range: 0-%d)\n", yylineno, idx, base_name, sym->dimensions[0], sym->dimensions[0]-1);
        }
        int byte_offset = idx * elem_size;
        char* result = genvar();
        sprintf(result, "%d", byte_offset);
        return result;
    }
    if (all_constant && sym->dim_count > 1) {
        for (int i = 0; i < idx_count && i < sym->dim_count; i++) {
            int idx = atoi(idx_list[i]);
            if (idx < 0) {
                e = 1;
                sprintf(err+strlen(err), "Line %d: Index %d at dimension %d is negative for array %s\n", yylineno, idx, i, base_name);
            } else if (idx >= sym->dimensions[i] && sym->dimensions[i] > 0) {
                e = 1;
                sprintf(err+strlen(err), "Line %d: Index %d out of bounds at dimension %d for array %s (valid: 0-%d)\n", yylineno, idx, i, base_name, sym->dimensions[i]-1);
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

/* Return 1 if the string is a numeric or character literal (not a temp/variable) */
int isLiteral(char* str) {
    if (!str || *str == '\0') return 0;
    if (str[0] == '\'' && strlen(str) >= 3 && str[strlen(str)-1] == '\'') {
        return 1;
    }
    if (str[0] == '(') {
        char* closing = strchr(str, ')');
        if (closing) {
            char* value_part = closing + 1;
            while (*value_part == ' ') value_part++;
            return isLiteral(value_part);  
        }
    }
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
                "Line %d: Warning: Value %.0f out of range for char (valid range: -128 to 127)\n", yylineno, value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "short") == 0) {
        if (value < -32768 || value > 32767) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %.0f out of range for short (valid range: -32768 to 32767)\n", yylineno, value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "int") == 0) {
        if (value < -2147483648.0 || value > 2147483647.0) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %.0f out of range for int (valid range: -2147483648 to 2147483647)\n", yylineno, value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "long") == 0) {
        if (fabs(value) > 9.223372e18) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %.0f may be out of range for long\n", yylineno, value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "float") == 0) {
        if (value > FLT_MAX || value < -FLT_MAX) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %g exceeds float range [-%g, %g] (will be inf)\n",
                yylineno, value, FLT_MAX, FLT_MAX);
            has_warning = 1;
        } else if (value != 0.0 && fabs(value) < FLT_MIN) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %g is too small for float (will underflow to 0)\n",
                yylineno, value);
            has_warning = 1;
        }
    }
    else if (strcmp(target_type, "double") == 0) {
        if (isinf(value) || value > DBL_MAX || value < -DBL_MAX) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %g exceeds double range (will be inf)\n",
                yylineno, value);
            has_warning = 1;
        } else if (value != 0.0 && fabs(value) < DBL_MIN) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Value %g is too small for double (will underflow to 0)\n",
                yylineno, value);
            has_warning = 1;
        }
    }
    return !has_warning;
}

int isNarrowingConversion(char* target_type, char* source_type) {
    int target_rank = getTypeRank(target_type);
    int source_rank = getTypeRank(source_type);
    if (target_rank > 0 && source_rank > 0) {
        return source_rank > target_rank;
    }
    return 0;
}

/* Type-check a binary expression; emit casts and set result type (usual arithmetic conv.) */
void checkType(struct Expr* op1, struct Expr* op2, char* opr1, char* opr2, char* type){
    char* base_op1 = getBaseType(op1->type);
    char* base_op2 = getBaseType(op2->type);
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


/* Type-check an assignment; emit cast TAC or narrowing warnings as needed */
void checkTypeAssign(struct Expr* op1, struct Expr* op2, char* opr){
    if (strcmp(op1->type, op2->type) == 0){ 
        strcpy(opr, ""); 
        return; 
    }
    char base_op1_type[100], base_op2_type[100];
    strcpy(base_op1_type, op1->type);
    strcpy(base_op2_type, op2->type);
    char* actual_op1 = base_op1_type;
    char* actual_op2 = base_op2_type;
    if (strncmp(base_op1_type, "const ", 6) == 0) actual_op1 = base_op1_type + 6;
    if (strncmp(base_op2_type, "const ", 6) == 0) actual_op2 = base_op2_type + 6;
    char* op1_base = getBaseType(actual_op1);
    char* op2_base = getBaseType(actual_op2);
    if (strcmp(op1_base, op2_base) == 0) { 
        strcpy(opr, ""); 
        return; 
    }
    char n1[100], n2[100];
    normalizeType(op1_base, n1);
    normalizeType(op2_base, n2);
    int op1_is_ptr = isPointerType(n1);
    int op2_is_ptr = isPointerType(n2);
    if (op1_is_ptr || op2_is_ptr) {
        if (op1_is_ptr && !op2_is_ptr) {
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
    e = 1;
    sprintf(err+strlen(err),
        "Line %d: Type error: incompatible pointer types '%s' and '%s'\n",
        yylineno, n2, n1);
}
        strcpy(opr, "");
        return;
    }
    int rank1 = getTypeRank(op1_base);
    int rank2 = getTypeRank(op2_base);
    if (rank1 > 0 && rank2 > 0) {
        if (rank2 > rank1) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Implicit narrowing conversion from %s to %s may lose data\n",
                yylineno, op2_base, op1_base);
        }
        if (isFloatingType(op2_base) && isIntegerType(op1_base)) {
            sprintf(err+strlen(err),
                "Line %d: Warning: Conversion from %s to %s will discard fractional part\n",
                yylineno, op2_base, op1_base);
        }
        if (isLiteral(op2->str)) {
            checkLiteralRange(op2->str, op1_base);
        }
    }
    if (isLiteral(op2->str)) {
        sprintf(opr, "(%s)%s", op1_base, op2->str);
    } else {
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
            if (strcmp(lhs, rhs) == 0) {
                g_identity++;
                sprintf(imcode[i], "%d // IDENTITY: %s = %s (eliminated)\n", line_num, lhs, rhs);
            }
        }
    }
}

//Removes assignments whose value is never used before being overwritten
void deadStoreElimination() {
    for (int i = 0; i < code - 1; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        {
            const char* alnp = line + strspn(line, "0123456789 ");
            if (strncmp(alnp, "deref ", 6) == 0) continue;
        }
        int line_num; char lhs[100], rhs[100];
        if (sscanf(line, "%d %s = %[^\n]", &line_num, lhs, rhs) == 3) {
            if (strstr(rhs, "Call") != NULL || strstr(rhs, "PopParam") != NULL) continue;
            if (strstr(rhs, "ref ") != NULL || strstr(rhs, "deref ") != NULL) continue;
            for (int j = i + 1; j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                if (strstr(imcode[j], "if ") != NULL || strstr(imcode[j], "goto ") != NULL ||
                    strstr(imcode[j], "BeginFunc") != NULL ||
                    strstr(imcode[j], "EndFunc") != NULL) break;
                char check_line[10000]; strcpy(check_line, imcode[j]);
                char check_lhs[100];
                char* equals = strchr(check_line, '=');
                if (equals) {
                    char* rhs_part = equals + 1;
                    if (strstr(rhs_part, lhs) != NULL) break;
                } else {
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
                if (sscanf(check_line, "%*d %s =", check_lhs) == 1) {
                    if (strcmp(check_lhs, lhs) == 0) {
                        int enclosing_begin = -1;
                        for (int k = i - 1; k >= 0; k--) {
                            if (strstr(imcode[k], "BeginFunc") != NULL) {
                                enclosing_begin = k; break;
                            }
                        }
                        if (enclosing_begin >= 0 && is_ref_param(enclosing_begin, lhs))
                            break; 
                        g_dead_store++;
                        sprintf(imcode[i], "%d // DEAD STORE: %s = %s\n", line_num, lhs, rhs);
                        break;
                    }
                }
            }
        }
    }
}

/* If two temps load the same variable, replace the second with the first if rhs not changed */
void redundantLoadElimination() {
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
            if (strchr(rhs, '+') != NULL || strchr(rhs, '-') != NULL ||
                strchr(rhs, '*') != NULL || strchr(rhs, '/') != NULL ||
                strchr(rhs, '%') != NULL || strchr(rhs, '&') != NULL ||
                strchr(rhs, '|') != NULL || strchr(rhs, '^') != NULL ||
                strstr(rhs, "<<") != NULL || strstr(rhs, ">>") != NULL ||
                strstr(rhs, "Call") != NULL) continue;
            if (isNumericConstant(rhs) || isLiteral(rhs)) continue;
            int lhs_len = strlen(lhs);
            int rhs_len = strlen(rhs);
            for (int j = i + 1; j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                if (strstr(imcode[j], "if ")      != NULL ||
                    strstr(imcode[j], "goto ")     != NULL ||
                    strstr(imcode[j], "Return")    != NULL ||
                    strstr(imcode[j], "BeginFunc") != NULL ||
                    strstr(imcode[j], "EndFunc")   != NULL) break;
                if (strstr(imcode[j], " ref ")   != NULL) break;
                if (strstr(imcode[j], " deref ") != NULL) break;
                {
                    const char* alnp_j = imcode[j] + strspn(imcode[j], "0123456789 ");
                    if (strncmp(alnp_j, "deref ", 6) == 0) break;
                }
                if (is_jump_target[j]) break;
                char jline[10000]; strcpy(jline, imcode[j]);
                int j_line_num; char j_lhs[100], j_rhs[100];
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
                if (sscanf(jline, "%*d %s =", j_lhs) == 1) {
                    if (strcmp(j_lhs, rhs) == 0) break;
                    if (strncmp(j_lhs, rhs, rhs_len) == 0 &&
                        (j_lhs[rhs_len] == '[' || j_lhs[rhs_len] == '\0')) break;
                }
                if (sscanf(jline, "%d %s = %[^\n]", &j_line_num, j_lhs, j_rhs) == 3) {
                    char* je = j_rhs + strlen(j_rhs) - 1;
                    while (je > j_rhs && (*je == ' ' || *je == '\n')) { *je = '\0'; je--; }
                    if (strcmp(j_rhs, rhs) == 0 && strcmp(j_lhs, lhs) != 0) {
                        g_redund_load++;
                        sprintf(imcode[j], "%d %s = %s\n", j_line_num, j_lhs, lhs);
                    }
                }
            }
        }
    }
}

/*Remove adjacent redundant copy sequences like t1=x; t1=x; t2=t1 where t2 isn't used*/
void peepholeOptimization(){
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
                if (strcmp(lhs1, rhs2) == 0 && strcmp(rhs1, lhs2) == 0) {
                    g_peephole++;
                    sprintf(imcode[i+1], "%d // PEEPHOLE: %s = %s (redundant peephole)\n", line_num2, lhs2, rhs2);
                }
            }
        }
    }
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        if (strstr(imcode[i], "// PEEPHOLE") != NULL) continue;
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
                            g_peephole++;
                            sprintf(imcode[j], "%d // PEEPHOLE: %s = %s (redundant peephole)\n", check_line_num, check_lhs, check_rhs);
                        }
                        break;
                    }
                    if (strcmp(check_lhs, rhs) == 0) break;
                }
            }
        }
    }
}


/* Replace x*2^k with x<<k (or x+x for *2), x/2^k with x>>k */
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
                    g_strength_red++;
                    if (constant == 2) sprintf(imcode[i], "%d %s = %s + %s\n", line_num, result, op1, op1);
                    else sprintf(imcode[i], "%d %s = %s << %d\n", line_num, result, op1, shift);
                    continue;
                }
            }
            if (strcmp(op, "/") == 0 && constant > 0) {
                if ((constant & (constant - 1)) == 0) {
                    int shift = 0; int temp = constant;
                    while (temp > 1) { temp >>= 1; shift++; }
                    g_strength_red++;
                    sprintf(imcode[i], "%d %s = %s >> %d\n", line_num, result, op1, shift);
                    continue;
                }
            }
        }
    }
}

/* Fold identities: x*1→x, x+0→x, x-x→0, x^x→0, x&0→0, etc. */
void algebraicSimplification() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1[100], op[10], op2[100];
        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1, op, op2) == 5) {
            if (strcmp(op,"*")==0 && strcmp(op2,"1")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"*")==0 && strcmp(op1,"1")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"*")==0 && strcmp(op2,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"*")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if ((strcmp(op,"+")==0||strcmp(op,"-")==0) && strcmp(op2,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"+")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"-")==0 && strcmp(op1,op2)==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"/")==0 && strcmp(op2,"1")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"/")==0 && strcmp(op1,op2)==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            if (strcmp(op,"/")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"%")==0 && strcmp(op2,"1")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  
            if (strcmp(op,"%")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  
            if (strcmp(op,"%")==0 && strcmp(op1,op2)==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  
            if (strcmp(op,"&")==0 && (strcmp(op2,"0")==0||strcmp(op1,"0")==0)){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"&")==0 && strcmp(op1,op2)==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  
            if (strcmp(op,"|")==0 && strcmp(op2,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"|")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"|")==0 && strcmp(op1,op2)==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  
            if (strcmp(op,"^")==0 && strcmp(op2,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"^")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"^")==0 && strcmp(op1,op2)==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }  
            if (strcmp(op,"<<")==0 && strcmp(op2,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; } 
            if (strcmp(op,"<<")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }        
            if (strcmp(op,">>")==0 && strcmp(op2,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }  
            if (strcmp(op,">>")==0 && strcmp(op1,"0")==0){ g_alg_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }        
        }
    }
}

/* Evaluate compile-time-constant branches and mark always-false ones dead */
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
                int is_loop_header = 0;
                for (int j = i + 1; j < code; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    char* gp = strstr(imcode[j], "goto");
                    if (!gp) continue;
                    char* tp = gp + 4;
                    while (*tp == ' ' || *tp == '\t') tp++;
                    if (!isdigit(*tp)) continue;
                    int target = atoi(tp);
                    if (target <= i) {          
                        is_loop_header = 1;
                        break;
                    }
                }
                if (is_loop_header) continue;  
                char resolved_op1[100], resolved_op2[100];
                strcpy(resolved_op1, op1);
                strcpy(resolved_op2, op2);
                int op1_is_truly_constant = 1;
                int op2_is_truly_constant = 1;
                if (!isNumericConstant(op1)) {
                    int assignment_count = 0;
                    for (int j = 0; j < i; j++) {
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
                if (!isNumericConstant(op2)) {
                    int assignment_count = 0;
                    for (int j = 0; j < i; j++) {
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
                int cond_assign_pattern = 0;
                if (op1_is_truly_constant || op2_is_truly_constant) {
                    char* goto_scan = strstr(rest, "goto");
                    int goto_tgt = -1;
                    if (goto_scan) {
                        char* tp2 = goto_scan + 4;
                        while (*tp2 == ' ' || *tp2 == '\t') tp2++;
                        if (isdigit(*tp2)) goto_tgt = atoi(tp2);
                    }
                    if (goto_tgt > i) {
                        for (int j = i + 1; j < code && j < goto_tgt + 1; j++) {
                            if (strstr(imcode[j], "// DEAD") != NULL) continue;
                            char check_lhs2[100];
                            int jlnum = -1;
                            sscanf(imcode[j], "%d", &jlnum);
                            if (jlnum >= goto_tgt) break; 
                            if (sscanf(imcode[j], "%*d %s =", check_lhs2) == 1) {
                                if ((!isNumericConstant(op1) && strcmp(check_lhs2, op1) == 0) ||
                                    (!isNumericConstant(op2) && strcmp(check_lhs2, op2) == 0)) {
                                    cond_assign_pattern = 1;
                                    break;
                                }
                            }
                        }
                    }
                }
                if (cond_assign_pattern) continue; 
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
                            g_const_fold_cond++;
                            sprintf(imcode[i], "%d %s // FOLDED: if %s %s %s always true\n", 
                                    line_num, goto_ptr, resolved_op1, op, resolved_op2);
                        }
                    } else {
                        g_const_fold_cond++;
                        g_dead_branch++;
                        sprintf(imcode[i], "%d // DEAD BRANCH: if %s %s %s always false\n", 
                                line_num, resolved_op1, op, resolved_op2);
                    }
                }
            }
        }
    }
}



static int parse_assign(const char* line,
                         char* lhs, char* op, char* a1, char* a2)
{
    lhs[0] = op[0] = a1[0] = a2[0] = '\0';
    if (strstr(line, "// DEAD") || strstr(line, "// IDENTITY")) return 0;
    char buf[10000]; strcpy(buf, line);
    char *p = buf;
    while (*p == ' ') p++;
    while (*p && isdigit((unsigned char)*p)) p++;
    while (*p == ' ') p++;
    if (strncmp(p,"if ",3)==0 || strncmp(p,"goto ",5)==0 ||
        strncmp(p,"BeginFunc",9)==0 || strncmp(p,"EndFunc",7)==0 ||
        strncmp(p,"Return",6)==0 || strncmp(p,"Call ",5)==0 ||
        strncmp(p,"PushParam",9)==0 || strncmp(p,"PopParam",8)==0 ||
        strncmp(p,"printint",8)==0 || strncmp(p,"printfloat",10)==0 ||
        strncmp(p,"printchar",9)==0 || strncmp(p,"printstring",11)==0 ||
        strncmp(p,"inputint",8)==0 || strncmp(p,"inputfloat",10)==0)
        return 0;
    char *eq = strchr(p, '=');
    if (!eq) return 0;
    int ll = (int)(eq - p);
    strncpy(lhs, p, ll); lhs[ll] = '\0';
    { int k=strlen(lhs)-1; while(k>=0&&lhs[k]==' ')lhs[k--]='\0'; }
    if (!lhs[0]) return 0;
    char *rhs = eq + 1;
    while (*rhs == ' ') rhs++;
    { int k=strlen(rhs)-1; while(k>=0&&(rhs[k]=='\n'||rhs[k]==' '))rhs[k--]='\0'; }
    if (strncmp(rhs,"Call ",5)==0 || rhs[0]=='(') return 0;
    char w1[200]="", w2[10]="", w3[200]="";
    int n = sscanf(rhs, "%s %s %s", w1, w2, w3);
    if (n == 3 && (strcmp(w2,"+")==0||strcmp(w2,"-")==0||
                   strcmp(w2,"*")==0||strcmp(w2,"/")==0||
                   strcmp(w2,"%")==0)) {
        strcpy(op, w2); strcpy(a1, w1); strcpy(a2, w3);
    } else {
        strcpy(op, "="); strcpy(a1, rhs); a2[0]='\0';
    }
    return 1;
}
static int tac_is_numeric(const char* s) {
    if (!s||!s[0]) return 0;
    const char* p = s;
    if (*p=='-'||*p=='+') p++;
    int d=0,dot=0;
    while(*p){ if(isdigit((unsigned char)*p))d=1;
               else if(*p=='.'&&!dot)dot=1; else return 0; p++; }
    return d;
}

/* Insert a blank TAC slot at position ins, renumber all lines and fix goto targets - Insert a new TAC instruction at position ins*/
static void imcode_insert_at(int ins) {
    for (int k = code; k > ins; k--)
        strcpy(imcode[k], imcode[k-1]);
    imcode[ins][0] = '\0';
    code++;
    for (int k = 0; k < code; k++) {
        if (imcode[k][0] == '\0') continue;
        char tmp[10000];
        int old_num;
        if (sscanf(imcode[k], "%d ", &old_num) == 1) {
            char *rest = imcode[k];
            while (*rest && isdigit((unsigned char)*rest)) rest++;
            while (*rest == ' ') rest++;
            sprintf(tmp, "%d %s", k, rest);
            strcpy(imcode[k], tmp);
        }
    }
    for (int k = 0; k < code; k++) {
        char *gp = strstr(imcode[k], "goto ");
        if (gp) {
            char *tp = gp + 5;
            while (*tp == ' ') tp++;
            if (isdigit((unsigned char)*tp)) {
                int tgt = atoi(tp);
                if (tgt >= ins) {
                    char tmp2[10000];
                    int before_len = (int)(tp - imcode[k]);
                    strncpy(tmp2, imcode[k], before_len);
                    tmp2[before_len] = '\0';
                    char *after = tp;
                    while (*after && isdigit((unsigned char)*after)) after++;
                    sprintf(tmp2 + before_len, "%d%s", tgt+1, after);
                    strcpy(imcode[k], tmp2);
                }
            }
        }
    }
}


#define LICM_MAX_WRITTEN  512
#define LICM_MAX_HOIST    256
static int licm_in_written(char written[][100], int wcnt, const char* name) {
    if (!name || !name[0]) return 0;
    for (int i = 0; i < wcnt; i++)
        if (strcmp(written[i], name) == 0) return 1;
    return 0;
}
static int licm_dominates_backedge(int body_first, int candidate) {
    for (int k = body_first; k < candidate; k++) {
        if (strstr(imcode[k], "// DEAD") != NULL) continue;
        char* gp = strstr(imcode[k], "goto");
        if (!gp) continue;
        char* tp = gp + 4;
        while (*tp == ' ' || *tp == '\t') tp++;
        if (!isdigit((unsigned char)*tp)) continue;
        int tgt = atoi(tp);
        if (tgt > candidate) return 0;
    }
    return 1;
}

/*
detect loops using back-edges, identify invariant computations using a written-variable set and 
iterative marking, and hoist them safely outside while preserving control flow*/

void loopInvariantCodeMotion() {
    int hoisted_total = 0;
    int hoisted_this_round;
    do {
        hoisted_this_round = 0;
        int search_start = 0;   
        while (1) {
            int loop_start = -1;
            int loop_end   = -1;
            int loop_header_lnum = -1;
            for (int i = search_start; i < code && loop_start == -1; i++) {
                if (strstr(imcode[i], "// DEAD") != NULL) continue;
                int ln_i;
                if (sscanf(imcode[i], "%d", &ln_i) != 1) continue;
                for (int j = i + 1; j < code; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    char* gp = strstr(imcode[j], "goto");
                    if (!gp) continue;
                    char* ip = strstr(imcode[j], " if ");
                    if (ip && ip < gp) continue;
                    char* tp = gp + 4;
                    while (*tp == ' ' || *tp == '\t') tp++;
                    if (!isdigit(*tp)) continue;
                    int tgt = atoi(tp);
                    if (tgt == ln_i) {
                        loop_start       = i;
                        loop_end         = j;
                        loop_header_lnum = ln_i;
                        break;
                    }
                }
            }
            if (loop_start == -1) break;
            int body_first = loop_start + 1;
            int body_last  = loop_end;        
            if (body_first > body_last) {
                search_start = loop_start + 1;
                continue;
            }
        char written[LICM_MAX_WRITTEN][100];
        int  wcnt = 0;
        for (int i = body_first; i <= body_last; i++) {
            if (strstr(imcode[i], "// DEAD") != NULL) continue;
            int ln; char lhs[100];
            if (sscanf(imcode[i], "%d %s =", &ln, lhs) == 2) {
                if (strchr(lhs, '[') != NULL) continue;
                int found = 0;
                for (int k = 0; k < wcnt; k++)
                    if (strcmp(written[k], lhs) == 0) { found = 1; break; }
                if (!found && wcnt < LICM_MAX_WRITTEN)
                    strcpy(written[wcnt++], lhs);
            }
        }
        for (int i = 0; i < code; i++) {
            if (i >= body_first && i <= body_last) continue; 
            if (strstr(imcode[i], "// DEAD") != NULL) continue;
            char *gp2 = strstr(imcode[i], "goto");
            if (!gp2) continue;
            char *ip2 = strstr(imcode[i], " if ");
            if (ip2 && ip2 < gp2) continue;  
            char *tp2 = gp2 + 4;
            while (*tp2 == ' ' || *tp2 == '\t') tp2++;
            if (!isdigit((unsigned char)*tp2)) continue;
            int enc_tgt = atoi(tp2);
            if (enc_tgt < loop_start && i > loop_end) {
                for (int j = enc_tgt; j <= i; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    int ln2; char elhs[100];
                    if (sscanf(imcode[j], "%d %s =", &ln2, elhs) == 2) {
                        if (strchr(elhs, '[') != NULL) continue;
                        int found2 = 0;
                        for (int k = 0; k < wcnt; k++)
                            if (strcmp(written[k], elhs) == 0) { found2 = 1; break; }
                        if (!found2 && wcnt < LICM_MAX_WRITTEN)
                            strcpy(written[wcnt++], elhs);
                    }
                }
            }
        }
        int inv[LICM_MAX_HOIST];
        int inv_cnt    = 0;
        int marked[10000];  
        memset(marked, 0, sizeof(marked));
        int new_found;
        do {
            new_found = 0;
            for (int i = body_first; i < body_last && inv_cnt < LICM_MAX_HOIST; i++) {
                if (marked[i]) continue;                               
                if (strstr(imcode[i], "// DEAD") != NULL) continue;
                if (strstr(imcode[i], "goto")      != NULL) continue;
                if (strstr(imcode[i], " if ")       != NULL) continue;
                if (strstr(imcode[i], "Call")       != NULL) continue;
                if (strstr(imcode[i], "Return")     != NULL) continue;
                if (strstr(imcode[i], "PushParam")  != NULL) continue;
                if (strstr(imcode[i], "PopParam")   != NULL) continue;
                if (strstr(imcode[i], "BeginFunc")  != NULL) continue;
                if (strstr(imcode[i], "EndFunc")    != NULL) continue;
                if (strstr(imcode[i], "print")      != NULL) continue;
                if (strstr(imcode[i], "ALLOC")      != NULL) continue;
                if (strstr(imcode[i], "CALLOC")     != NULL) continue;
                if (strstr(imcode[i], "REALLOC")    != NULL) continue;
                if (strstr(imcode[i], "FREE")       != NULL) continue;
                if (strstr(imcode[i], " deref ")    != NULL) continue;
                {
                    const char* afn = imcode[i];
                    while (*afn && isdigit((unsigned char)*afn)) afn++;
                    while (*afn == ' ') afn++;
                    if (strncmp(afn, "deref ", 6) == 0) continue;
                }
                char line[10000]; strcpy(line, imcode[i]);
                int  ln; char lhs[100], rhs[10000];
                if (sscanf(line, "%d %s = %[^\n]", &ln, lhs, rhs) != 3) continue;
                if (strchr(lhs, '[') != NULL) continue;
                if (!licm_dominates_backedge(body_first, i)) continue;
                int wc = 0;
                for (int j = body_first; j <= body_last; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    char jlhs[100];
                    if (sscanf(imcode[j], "%*d %s =", jlhs) == 1 &&
                        strcmp(jlhs, lhs) == 0) wc++;
                }
                if (wc != 1) continue;
                char* rend = rhs + strlen(rhs) - 1;
                while (rend > rhs && (*rend == ' ' || *rend == '\n' || *rend == '\r'))
                    *rend-- = '\0';
                char op1[100] = "", binop[20] = "", op2[100] = "";
                int nf = sscanf(rhs, "%s %s %s", op1, binop, op2);
                if (nf < 1) continue;
                if (strchr(op1,'(')||strchr(op1,'[')) continue;
                if (nf == 3 && (strchr(op2,'(')||strchr(op2,'['))) continue;
                int op1_ok = !licm_in_written(written, wcnt, op1);
                if (!op1_ok) {
                    int writer_marked = 0, writer_count = 0;
                    for (int j = body_first; j <= body_last; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char jlhs[100];
                        if (sscanf(imcode[j], "%*d %s =", jlhs) == 1 &&
                            strcmp(jlhs, op1) == 0) {
                            writer_count++;
                            if (marked[j]) writer_marked = 1;
                        }
                    }
                    op1_ok = (writer_count == 1 && writer_marked);
                }
                if (!op1_ok) continue;
                int op2_ok = 1;
                if (nf == 3) {
                    op2_ok = !licm_in_written(written, wcnt, op2);
                    if (!op2_ok) {
                        int writer_marked = 0, writer_count = 0;
                        for (int j = body_first; j <= body_last; j++) {
                            if (strstr(imcode[j], "// DEAD") != NULL) continue;
                            char jlhs[100];
                            if (sscanf(imcode[j], "%*d %s =", jlhs) == 1 &&
                                strcmp(jlhs, op2) == 0) {
                                writer_count++;
                                if (marked[j]) writer_marked = 1;
                            }
                        }
                        op2_ok = (writer_count == 1 && writer_marked);
                    }
                }
                if (!op2_ok) continue;
                marked[i]        = 1;
                inv[inv_cnt++]   = i;
                new_found        = 1;
            }
        } while (new_found && inv_cnt < LICM_MAX_HOIST);
        if (inv_cnt == 0) {
                search_start = loop_start + 1;
                continue;
            }
            if (code + inv_cnt >= 10000) {
                search_start = loop_start + 1;
                continue;
            }
        for (int k = code - 1; k >= loop_start; k--)
            strcpy(imcode[k + inv_cnt], imcode[k]);
        code += inv_cnt;
        for (int k = 0; k < code; k++) {
            if (imcode[k][0] == '\0') continue;
            int old_num;
            if (sscanf(imcode[k], "%d ", &old_num) != 1) continue;
            char tmp[10000];
            char *rest = imcode[k];
            while (*rest && isdigit((unsigned char)*rest)) rest++;
            while (*rest == ' ') rest++;
            sprintf(tmp, "%d %s", k, rest);
            strcpy(imcode[k], tmp);
        }
        for (int k = 0; k < code; k++) {
            if (strstr(imcode[k], "// DEAD") != NULL) continue;
            char *gp = strstr(imcode[k], "goto ");
            if (!gp) continue;
            char *tp = gp + 5;
            while (*tp == ' ') tp++;
            if (!isdigit((unsigned char)*tp)) continue;
            int tgt = atoi(tp);
            int new_tgt = -1;
            if (tgt == loop_header_lnum) {
                new_tgt = loop_start + inv_cnt;
            } else if (tgt > loop_header_lnum) {
                new_tgt = tgt + inv_cnt;
            }
            if (new_tgt != -1) {
                char tmp2[10000];
                int before_len = (int)(tp - imcode[k]);
                strncpy(tmp2, imcode[k], before_len);
                tmp2[before_len] = '\0';
                char *after = tp;
                while (*after && isdigit((unsigned char)*after)) after++;
                sprintf(tmp2 + before_len, "%d%s", new_tgt, after);
                strcpy(imcode[k], tmp2);
            }
        }
        for (int h = 0; h < inv_cnt; h++)
            inv[h] += inv_cnt;
        for (int h = 0; h < inv_cnt; h++) {
            int src = inv[h];
            char line[10000]; strcpy(line, imcode[src]);
            int  orig_ln; char lhs[100], rhs[10000];
            sscanf(line, "%d %s = %[^\n]", &orig_ln, lhs, rhs);
            char* rend = rhs + strlen(rhs) - 1;
            while (rend > rhs && (*rend == ' ' || *rend == '\n' || *rend == '\r'))
                *rend-- = '\0';
            int slot = loop_start + h;
            sprintf(imcode[slot], "%d %s = %s\n", slot, lhs, rhs);
            // printf(imcode[src],  "%d // DEAD HOIST: moved to line %d\n", orig_ln, slot);
                       g_dead_hoist++;
                       sprintf(imcode[src],  "%d // DEAD HOIST: moved up\n", orig_ln);
            hoisted_this_round++;
        }
        hoisted_total += hoisted_this_round;
            break;
        } 
    } while (hoisted_this_round > 0);
}


#define IVE_MAX_LOOPS 64
#define IVE_MAX_BIVS  16
#define IVE_MAX_DIVS  64
typedef struct {
    int header;      
    int footer;      
    int exit_test;   
} IVE_LoopInfo;
typedef struct {
    char var[64];       
    char step_str[32];  
    double step;        
    int  update_idx;    
    char op[4];         
} IVE_BIV;
typedef struct {
    char result[64];    
    char biv_name[64];  
    char coeff_str[64]; 
    double coeff;       
    int  quad_idx;      
} IVE_DIV;
static IVE_LoopInfo ive_loops[IVE_MAX_LOOPS];
static int          ive_loop_cnt;
static IVE_BIV      ive_bivs[IVE_MAX_LOOPS][IVE_MAX_BIVS];
static int          ive_biv_cnt[IVE_MAX_LOOPS];
static IVE_DIV      ive_divs[IVE_MAX_LOOPS][IVE_MAX_DIVS];
static int          ive_div_cnt[IVE_MAX_LOOPS];
static int          ive_var_id = 0;
static void ive_new_var(char *buf) {
    sprintf(buf, "iv%d", ive_var_id++);
}
static int ive_parse_line(const char *raw,
                          char *lhs, char *op, char *a1, char *a2)
{
    lhs[0] = op[0] = a1[0] = a2[0] = '\0';
    if (!raw || raw[0] == '\0') return 0;
    if (strstr(raw, "// DEAD")) return 0;
    char buf[10000]; strcpy(buf, raw);
    char *p = buf;
    while (*p == ' ') p++;
    while (*p && isdigit((unsigned char)*p)) p++; 
    while (*p == ' ') p++;
    if (strncmp(p,"if ",3)==0 || strncmp(p,"goto ",5)==0 ||
        strncmp(p,"BeginFunc",9)==0 || strncmp(p,"EndFunc",7)==0 ||
        strncmp(p,"Return",6)==0 || strncmp(p,"Call ",5)==0 ||
        strncmp(p,"PushParam",9)==0 || strncmp(p,"PopParam",8)==0 ||
        strncmp(p,"print",5)==0 || strncmp(p,"input",5)==0)
        return 0;
    char *eq = strchr(p, '=');
    if (!eq) return 0;
    int ll = (int)(eq - p);
    strncpy(lhs, p, ll); lhs[ll] = '\0';
    { int k = strlen(lhs)-1; while (k>=0 && lhs[k]==' ') lhs[k--] = '\0'; }
    if (!lhs[0]) return 0;
    char *rhs = eq + 1;
    while (*rhs == ' ') rhs++;
    { int k = strlen(rhs)-1;
      while (k>=0 && (rhs[k]=='\n'||rhs[k]==' ')) rhs[k--]='\0'; }
    if (strncmp(rhs,"Call ",5)==0 || rhs[0]=='(') return 0;
    char w1[200]="", w2[16]="", w3[200]="";
    int n = sscanf(rhs, "%s %s %s", w1, w2, w3);
    if (n == 3 && (strcmp(w2,"+")==0 || strcmp(w2,"-")==0 ||
                   strcmp(w2,"*")==0 || strcmp(w2,"/")==0 ||
                   strcmp(w2,"<<")==0 || strcmp(w2,">>")==0)) {
        strcpy(op, w2); strcpy(a1, w1); strcpy(a2, w3);
    } else {
        strcpy(op, "="); strcpy(a1, rhs); a2[0] = '\0';
    }
    return 1;
}
static void ive_make_copy(int idx, const char *result, const char *src)
{
    sprintf(imcode[idx], "%d %s = %s\n", idx, result, src);
}
static int is_loop_invariant_var(const char *varname,
                                  int body_start, int body_end,
                                  IVE_BIV *bivs, int biv_cnt,
                                  int depth)
{
    if (depth > 4) return 0;  
    for (int b = 0; b < biv_cnt; b++)
        if (strcmp(bivs[b].var, varname) == 0) return 0;
    int write_count = 0;
    for (int w = body_start; w <= body_end; w++) {
        char wl[64]="", wo[8]="", wa1[200]="", wa2[200]="";
        if (!ive_parse_line(imcode[w], wl, wo, wa1, wa2)) continue;
        if (strcmp(wl, varname) != 0) continue;
        write_count++;
        if (!isNumericConstant(wa1) && wa1[0]) {
            if (!is_loop_invariant_var(wa1, body_start, body_end,
                                       bivs, biv_cnt, depth+1))
                return 0;
        }
        if (!isNumericConstant(wa2) && wa2[0]) {
            if (!is_loop_invariant_var(wa2, body_start, body_end,
                                       bivs, biv_cnt, depth+1))
                return 0;
        }
    }
    return 1;
}

/* Replace strength-reduced loop multiplications with additive induction variables */
int inductionVariableElimination(void)
{
    ive_loop_cnt = 0;
    int total    = 0;
    for (int i = 0; i < code && ive_loop_cnt < IVE_MAX_LOOPS; i++) {
        if (strstr(imcode[i], "// DEAD")) continue;
        char *gp = strstr(imcode[i], "goto");
        if (!gp) continue;
        char *ip = strstr(imcode[i], " if ");
        if (ip && ip < gp) continue;   
        char *tp = gp + 4;
        while (*tp == ' ' || *tp == '\t') tp++;
        if (!isdigit((unsigned char)*tp)) continue;
        int tgt_lnum = atoi(tp);
        int hdr = -1;
        for (int j = 0; j < i; j++) {
            if (strstr(imcode[j], "// DEAD")) continue;
            int ln = -1;
            sscanf(imcode[j], "%d ", &ln);
            if (ln == tgt_lnum) { hdr = j; break; }
        }
        if (hdr < 0) continue;
        IVE_LoopInfo *lp = &ive_loops[ive_loop_cnt];
        lp->header    = hdr;
        lp->footer    = i;
        lp->exit_test = -1;
        for (int j = hdr; j <= i; j++) {
            if (strstr(imcode[j], " if ") && strstr(imcode[j], "goto")) {
                lp->exit_test = j;
                break;
            }
        }
        ive_biv_cnt[ive_loop_cnt] = 0;
        ive_div_cnt[ive_loop_cnt] = 0;
        ive_loop_cnt++;
    }
    if (ive_loop_cnt == 0) {
        //printf("[IVE] No loops detected.\n");
        return 0;
    }
    for (int a = 0; a < ive_loop_cnt - 1; a++) {
        for (int b = a + 1; b < ive_loop_cnt; b++) {
            int sz_a = ive_loops[a].footer - ive_loops[a].header;
            int sz_b = ive_loops[b].footer - ive_loops[b].header;
            if (sz_a > sz_b) {
                IVE_LoopInfo tmp = ive_loops[a];
                ive_loops[a] = ive_loops[b];
                ive_loops[b] = tmp;
                int tc;
                tc = ive_biv_cnt[a]; ive_biv_cnt[a] = ive_biv_cnt[b]; ive_biv_cnt[b] = tc;
                tc = ive_div_cnt[a]; ive_div_cnt[a] = ive_div_cnt[b]; ive_div_cnt[b] = tc;
            }
        }
    }
    for (int li = 0; li < ive_loop_cnt; li++) {
        IVE_LoopInfo *lp = &ive_loops[li];
        int body_start = lp->header + 1;
        int body_end   = lp->footer - 1;
        if (body_start > body_end) continue;
        int bc = 0;
        for (int i = body_start; i <= body_end && bc < IVE_MAX_BIVS; i++) {
            int in_inner = 0;
            for (int x = 0; x < ive_loop_cnt; x++) {
                if (x == li) continue;
                int sz_x  = ive_loops[x].footer - ive_loops[x].header;
                int sz_li = ive_loops[li].footer - ive_loops[li].header;
                if (sz_x >= sz_li) continue;
                if (i > ive_loops[x].header && i <= ive_loops[x].footer) {
                    in_inner = 1;
                    i = ive_loops[x].footer;
                    break;
                }
            }
            if (in_inner) continue;
            char lhs[64]="", op[8]="", a1[200]="", a2[200]="";
            if (!ive_parse_line(imcode[i], lhs, op, a1, a2)) continue;
            if ((strcmp(op,"+")==0 || strcmp(op,"-")==0) &&
                lhs[0] && isNumericConstant(a2))
            {
                if (strcmp(a1, lhs) == 0) {
                    IVE_BIV *b = &ive_bivs[li][bc++];
                    strncpy(b->var,      lhs, 63);
                    strncpy(b->step_str, a2,  31);
                    strncpy(b->op,       op,  3);
                    b->step       = (strcmp(op,"-")==0) ? -atof(a2) : atof(a2);
                    b->update_idx = i;
                } else {
                    for (int k = i+1; k <= body_end; k++) {
                        char lhs2[64]="", op2[8]="", a12[200]="", a22[200]="";
                        if (!ive_parse_line(imcode[k], lhs2, op2, a12, a22)) continue;
                        if (strcmp(op2,"=")==0 && a22[0]=='\0' &&
                            strcmp(a12, lhs)==0 && strcmp(lhs2, a1)==0)
                        {
                            IVE_BIV *b = &ive_bivs[li][bc++];
                            strncpy(b->var,      lhs2, 63);
                            strncpy(b->step_str, a2,   31);
                            strncpy(b->op,       op,   3);
                            b->step       = (strcmp(op,"-")==0) ? -atof(a2) : atof(a2);
                            b->update_idx = k;
                            break;
                        }
                    }
                }
            }
        }
        ive_biv_cnt[li] = bc;
        if (bc == 0) continue;
        int dc = 0;
        for (int i = body_start; i <= body_end && dc < IVE_MAX_DIVS; i++) {
            char lhs[64]="", op[8]="", a1[200]="", a2[200]="";
            if (!ive_parse_line(imcode[i], lhs, op, a1, a2)) continue;
            int is_shift = (strcmp(op,"<<")==0);
            if (strcmp(op,"*") != 0 && !is_shift) continue;
            if (!lhs[0]) continue;
            for (int b = 0; b < bc; b++) {
                const char *bname = ive_bivs[li][b].var;
                char coeff[64] = "";
                int  match = 0;
                if (is_shift) {
                    if (strcmp(a1, bname)==0 && isNumericConstant(a2)) {
                        int k = atoi(a2);
                        if (k >= 0 && k < 31) {
                            sprintf(coeff, "%d", 1 << k);
                            match = 1;
                        }
                    }
                } else {
                    if (strcmp(a1,bname)==0 && isNumericConstant(a2))
                        { strncpy(coeff,a2,63); match=1; }
                    else if (strcmp(a2,bname)==0 && isNumericConstant(a1))
                        { strncpy(coeff,a1,63); match=1; }
                    if (!match) {
                        const char *cand = NULL;
                        if (strcmp(a1,bname)==0 && a2[0] && !isNumericConstant(a2))
                            cand = a2;
                        else if (strcmp(a2,bname)==0 && a1[0] && !isNumericConstant(a1))
                            cand = a1;
                        if (cand) {
                            if (is_loop_invariant_var(cand, body_start, body_end,
                                                      ive_bivs[li], bc, 0))
                                { strncpy(coeff, cand, 63); match=1; }
                        }
                    }
                }
                if (!match) continue;
                const char *real_result = lhs;
                int          real_idx   = i;
                for (int k = i+1; k <= body_end; k++) {
                    char lhs2[64]="", op2[8]="", a12[200]="", a22[200]="";
                    if (!ive_parse_line(imcode[k], lhs2, op2, a12, a22)) continue;
                    if (strcmp(op2,"=")==0 && a22[0]=='\0' &&
                        strcmp(a12, lhs)==0)
                    {
                        real_result = imcode[k]; 
                        sscanf(imcode[k], "%*d %63s", lhs2);
                        char *eq2 = strchr(lhs2,'=');
                        if (eq2) *eq2='\0';
                        real_result = lhs2;      
                        real_idx    = k;
                        break;
                    }
                }
                char rr_buf[64];
                {
                    char tmp_lhs[64]="", tmp_op[8]="", tmp_a1[200]="", tmp_a2[200]="";
                    ive_parse_line(imcode[real_idx], tmp_lhs, tmp_op, tmp_a1, tmp_a2);
                    strncpy(rr_buf, tmp_lhs, 63);
                }
                int is_biv = 0;
                for (int bb = 0; bb < bc; bb++)
                    if (strcmp(rr_buf, ive_bivs[li][bb].var)==0) { is_biv=1; break; }
                if (is_biv) continue;
                {
                    char orig_lhs2[64]="", orig_op2[8]="", orig_a12[200]="", orig_a22[200]="";
                    ive_parse_line(imcode[i], orig_lhs2, orig_op2, orig_a12, orig_a22);
                    if (strcmp(rr_buf, orig_a12)==0 || strcmp(rr_buf, orig_a22)==0)
                        continue;
                }
                int write_count = 0;
                for (int w = body_start; w <= body_end; w++) {
                    char wlhs[64]="", wop[8]="", wa1[200]="", wa2[200]="";
                    if (!ive_parse_line(imcode[w], wlhs, wop, wa1, wa2)) continue;
                    if (strcmp(wlhs, rr_buf)==0) write_count++;
                }
                if (write_count > 1) continue;
                IVE_DIV *d = &ive_divs[li][dc++];
                strncpy(d->result,    rr_buf, 63);
                strncpy(d->biv_name,  bname,  63);
                strncpy(d->coeff_str, coeff,  63);
                d->coeff    = isNumericConstant(coeff) ? atof(coeff) : 0.0;
                d->quad_idx = real_idx;
                break;
            }
        }
        ive_div_cnt[li] = dc;
        if (dc == 0) continue;
        for (int di = 0; di < dc; di++) {
            IVE_DIV *dv = &ive_divs[li][di];
            body_start = lp->header + 1;
            body_end   = lp->footer - 1;
            IVE_BIV *bv = NULL;
            for (int b = 0; b < bc; b++)
                if (strcmp(ive_bivs[li][b].var, dv->biv_name)==0)
                    { bv = &ive_bivs[li][b]; break; }
            if (!bv) continue;
            char j_new[32];
            ive_new_var(j_new);
            int ins = lp->header;   
            imcode_insert_at(ins);  
            for (int x = 0; x < ive_loop_cnt; x++) {
                if (ive_loops[x].header   >= ins) ive_loops[x].header++;
                if (ive_loops[x].footer   >= ins) ive_loops[x].footer++;
                if (ive_loops[x].exit_test>= ins) ive_loops[x].exit_test++;
            }
            for (int b2 = 0; b2 < bc; b2++)
                if (ive_bivs[li][b2].update_idx >= ins)
                    ive_bivs[li][b2].update_idx++;
            for (int dj = di; dj < dc; dj++)
                if (ive_divs[li][dj].quad_idx >= ins)
                    ive_divs[li][dj].quad_idx++;
            bv = NULL;
            for (int b2 = 0; b2 < bc; b2++)
                if (strcmp(ive_bivs[li][b2].var, dv->biv_name)==0)
                    { bv = &ive_bivs[li][b2]; break; }
            char biv_init_str[64] = "0";
            int  biv_init_is_const = 1;   
            for (int k = 0; k < lp->header; k++) {
                char klhs[64]="", kop[8]="", ka1[200]="", ka2[200]="";
                if (!ive_parse_line(imcode[k], klhs, kop, ka1, ka2)) continue;
                if (strcmp(kop,"=")==0 && ka2[0]=='\0' &&
                    strcmp(klhs, bv->var)==0)
                {
                    strncpy(biv_init_str, ka1, 63);
                    biv_init_is_const = isNumericConstant(ka1);
                }
            }
            char div_init_str[128];
            char inc_str[128];
            if (isNumericConstant(dv->coeff_str)) {
                double biv_init = biv_init_is_const ? atof(biv_init_str) : 0.0;
                if (!biv_init_is_const) {
                    sprintf(imcode[ins], "%d %s = %s * %s\n",
                            ins, j_new, dv->coeff_str, biv_init_str);
                } else {
                    double div_init = biv_init * dv->coeff;
                    if (div_init == (long)div_init)
                        sprintf(div_init_str, "%ld", (long)div_init);
                    else
                        sprintf(div_init_str, "%f",  div_init);
                    sprintf(imcode[ins], "%d %s = %s\n", ins, j_new, div_init_str);
                }
                double inc_val = bv->step * dv->coeff;
                if (inc_val == (long)inc_val)
                    sprintf(inc_str, "%ld", (long)inc_val);
                else
                    sprintf(inc_str, "%f",  inc_val);

            } else {
                if (biv_init_is_const && strcmp(biv_init_str, "0") == 0) {
                    sprintf(imcode[ins], "%d %s = 0\n", ins, j_new);
                } else if (biv_init_is_const) {
                    sprintf(imcode[ins], "%d %s = %s * %s\n",
                            ins, j_new, dv->coeff_str, biv_init_str);
                } else {
                    sprintf(imcode[ins], "%d %s = %s * %s\n",
                            ins, j_new, dv->coeff_str, biv_init_str);
                }
                double step_abs = (bv->step < 0) ? -bv->step : bv->step;
                if (step_abs == 1.0) {
                    if (bv->step >= 0)
                        strncpy(inc_str, dv->coeff_str, 127);
                    else
                        sprintf(inc_str, "-%s", dv->coeff_str);
                } else {
                    strncpy(inc_str, dv->coeff_str, 127);
                }
            }
            int inc_pos = bv->update_idx + 1;
            imcode_insert_at(inc_pos);
            for (int x = 0; x < ive_loop_cnt; x++) {
                if (ive_loops[x].header   >= inc_pos) ive_loops[x].header++;
                if (ive_loops[x].footer   >= inc_pos) ive_loops[x].footer++;
                if (ive_loops[x].exit_test>= inc_pos) ive_loops[x].exit_test++;
            }
            for (int b2 = 0; b2 < bc; b2++)
                if (ive_bivs[li][b2].update_idx >= inc_pos)
                    ive_bivs[li][b2].update_idx++;
            for (int dj = di; dj < dc; dj++)
                if (ive_divs[li][dj].quad_idx >= inc_pos)
                    ive_divs[li][dj].quad_idx++;
            sprintf(imcode[inc_pos], "%d %s = %s + %s\n",
                    inc_pos, j_new, j_new, inc_str);
            ive_make_copy(dv->quad_idx, dv->result, j_new);
            g_ive++;
            total++;
        }
    }
    return total;
}

static int is_ref_param(int func_start_idx, const char *varname) {
    char fname[256] = "";
    sscanf(imcode[func_start_idx], "%*d BeginFunc %255s", fname);
    if (!fname[0]) return 0;
    Function *f = findFunction(fname);
    if (!f) return 0;
    for (Param *p = f->params; p; p = p->next)
        if (strcmp(p->name , varname) == 0)
            return p->is_ref;   
    return 0;
}


void copyPropagation() {
    int is_jump_target[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
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
            if (strstr(imcode[i], " ref ")   != NULL) continue;
            if (strstr(imcode[i], " deref ")  != NULL) continue;
            if (strncmp(imcode[i]+strspn(imcode[i],"0123456789 "), "deref ", 6) == 0) continue;
            if (strchr(rhs,'+')!=NULL||strchr(rhs,'-')!=NULL||strchr(rhs,'*')!=NULL||strchr(rhs,'/')!=NULL||
                strchr(rhs,'%')!=NULL||strchr(rhs,'&')!=NULL||strchr(rhs,'|')!=NULL||strchr(rhs,'^')!=NULL||
                strchr(rhs,'<')!=NULL||strchr(rhs,'>')!=NULL||strchr(rhs,'~')!=NULL||strchr(rhs,'(')!=NULL||
                strstr(rhs,"Call")!=NULL||strstr(rhs,"PopParam")!=NULL||strstr(rhs,"PushParam")!=NULL||
                strstr(rhs,"ALLOC")!=NULL||strstr(rhs,"CALLOC")!=NULL||strstr(rhs,"REALLOC")!=NULL) continue;
            if (is_jump_target[i]) {              
                int has_live_seq_pred = 0;
                if (i > 0) {
                    for (int k = i - 1; k >= 0; k--) {
                        if (strstr(imcode[k], "// DEAD") != NULL) continue;
                        char* gp = strstr(imcode[k], "goto");
                        char* ip = strstr(imcode[k], " if ");
                        int is_uncond_jump =
                            (gp != NULL && (ip == NULL || ip > gp)) ||
                            strstr(imcode[k], "Return") != NULL;
                        if (!is_uncond_jump) has_live_seq_pred = 1;
                        break;
                    }
                }
                if (has_live_seq_pred) continue;   
            }
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
                {
                    char kw[50], io_var[100];
                    if (sscanf(imcode[j], "%*d %49s %99s", kw, io_var) == 2) {
                        if ((strcmp(kw, "inputint")   == 0 ||
                             strcmp(kw, "inputfloat") == 0 ||
                             strcmp(kw, "inputchar")  == 0) &&
                            strcmp(io_var, lhs) == 0) {
                            first_modification = j;
                            break;
                        }
                    }
                }
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
            int has_goto_before_modification = 0;
            int goto_target = -1;
            for (int j = i + 1; j < first_modification && j < code; j++) {
                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                if (strstr(imcode[j], "goto") != NULL) {
                    int is_unconditional = (strstr(imcode[j], " if ") == NULL);
                    if (!is_unconditional) continue; 
                    char* goto_ptr = strstr(imcode[j], "goto");
                    char* ptr = goto_ptr + 4;
                    while (*ptr == ' ' || *ptr == '\t') ptr++;
                    if (isdigit(*ptr)) {
                        goto_target = atoi(ptr);
                        if (goto_target > first_modification || goto_target > i + 1) {
                            has_goto_before_modification = 1;
                            break;
                        }
                    }
                }
            }
            int safe_limit = (first_modification < rhs_first_modification) ? first_modification : rhs_first_modification;
            if (has_goto_before_modification && goto_target > safe_limit) {
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
                    safe_limit = (goto_target + 10 < func_end) ? goto_target + 10 : func_end;
                }
            }            
            int is_used = 0, last_use_line = -1;
            for (int j = i + 1; j < safe_limit && j < code; j++) {
                if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                char check_line[10000]; strcpy(check_line, imcode[j]);
                {
                    char ref_pat[200]; sprintf(ref_pat, "ref %s", lhs);
                    char* rp = strstr(check_line, ref_pat);
                    if (rp) {
                        char after_r = *(rp + strlen(ref_pat));
                        if (!isalnum((unsigned char)after_r) && after_r != '_')
                            { is_used = 1; last_use_line = j; }
                    }
                }
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
                            if (target <= last_use_line && j > target) {
                                use_inside_loop = 1;
                                break;
                            }
                        }
                    }
                }
                if (use_inside_loop && first_modification < func_end) continue;
                int has_use_at_jump_target = 0;
                for (int j = i + 1; j <= last_use_line && j < code; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    if (!is_jump_target[j]) continue;
                    char check_line[10000]; strcpy(check_line, imcode[j]);
                    int lhs_used_here = 0;
                    if (strstr(check_line, lhs) != NULL) {
                        char* pos = strstr(check_line, lhs);
                        while (pos) {
                            int is_whole = 1;
                            if (pos > check_line && (isalnum(*(pos-1)) || *(pos-1) == '_' || *(pos-1) == '\'')) is_whole = 0;
                            char after = *(pos + strlen(lhs));
                            if (isalnum(after) || after == '_' || after == '\'') is_whole = 0;
                            if (is_whole) { lhs_used_here = 1; break; }
                            pos = strstr(pos + 1, lhs);
                        }
                    }
                    if (!lhs_used_here) continue;
                    for (int k = 0; k < code; k++) {
                        if (strstr(imcode[k], "// DEAD") != NULL) continue;
                        char* gp = strstr(imcode[k], "goto");
                        if (!gp) continue;
                        char* tp = gp + 4;
                        while (*tp == ' ' || *tp == '\t') tp++;
                        if (!isdigit(*tp)) continue;
                        int gtgt = atoi(tp);
                        if (gtgt != j) continue;
                        if (k < i) { has_use_at_jump_target = 1; break; }
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
                if (rhs[0] == 't' && isdigit((unsigned char)rhs[1])) {
                    for (int k = 0; k < code; k++) {
                        if (strstr(imcode[k], "// DEAD") != NULL) continue;
                        char klhs[100];
                        if (sscanf(imcode[k], "%*d %s =", klhs) == 1 && strcmp(klhs, rhs) == 0) {
                            if (strstr(imcode[k], "ALLOC")   != NULL ||
                                strstr(imcode[k], "CALLOC")  != NULL ||
                                strstr(imcode[k], "REALLOC") != NULL) goto skip_prop;
                            break;
                        }
                    }
                }
                int can_propagate = 0;
                if (lhs[0] == 't' && isdigit(lhs[1])) can_propagate = 1;
                else if (is_constant && !used_in_subscript) can_propagate = 1;
                if (!can_propagate) continue;
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
                                if (k < i && gtarget > i) {
                                    inside_branch = 1;
                                    break;
                                }
                            }
                        }
                    }
                    if (inside_branch) continue;
                }              
                int is_user_var = !(lhs[0] == 't' && isdigit((unsigned char)lhs[1]));
                g_copy_prop++;
                for (int j = i + 1; j <= last_use_line && j < code && j < safe_limit; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    {
                        char* after_lnum_j = imcode[j] + strspn(imcode[j], "0123456789 ");
                        if (strncmp(after_lnum_j, "deref ", 6) == 0) continue;
                        char* eq_j = strchr(imcode[j], '=');
                        if (eq_j) {
                            char* rhs_j = eq_j + 1;
                            while (*rhs_j == ' ') rhs_j++;
                            if (strncmp(rhs_j, "ref ", 4) == 0 || strncmp(rhs_j, "deref ", 6) == 0) continue;
                        }
                    }
                    char new_line[10000]; strcpy(new_line, imcode[j]);
                    char* equals_sign = strchr(new_line, '=');
                    if (equals_sign == NULL) {                 
                        if (is_user_var) continue;
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
                }
            } else if (!is_used && is_constant) {
                             if (is_ref_param(func_start, lhs)) { /* skip */ }
                else {
                int globally_used = 0;
                for (int j = i + 1; j < func_end; j++) {
                    if (strstr(imcode[j], "// DEAD CODE:") != NULL) continue;
                    char check_line[10000]; strcpy(check_line, imcode[j]);
                    {
                        char ref_pat[200]; sprintf(ref_pat, "ref %s", lhs);
                        char* rp = strstr(check_line, ref_pat);
                        if (rp) {
                            char after_ref = *(rp + strlen(ref_pat));
                            if (!isalnum((unsigned char)after_ref) && after_ref != '_')
                                { globally_used = 1; break; }
                        }
                    }
                    char* eq = strchr(check_line, '=');
                    char* search_start;
                    if (eq == NULL) {
                        search_start = check_line;
                    } else {
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
                if (!globally_used) {
                    g_dead_const++;
                    sprintf(imcode[i], "%d // DEAD CONST: %s = %s\n", line_num, lhs, rhs);
                }
                } 
            }
        skip_prop:;      
        }      
    }
}

/* Simplify logical expressions: x&&1-x, x||0-x, x==x-1, etc. */
void booleanSimplification() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1[100], op[10], op2[100];
        if (sscanf(line, "%d %s = %s %s %s", &line_num, result, op1, op, op2) == 5) {
            if (strcmp(op,"&&")==0 && strcmp(op1,"1")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"&&")==0 && strcmp(op2,"1")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"&&")==0 && strcmp(op1,"0")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"&&")==0 && strcmp(op2,"0")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"&&")==0 && strcmp(op1,op2)==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"||")==0 && strcmp(op1,"0")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op2); continue; }
            if (strcmp(op,"||")==0 && strcmp(op2,"0")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"||")==0 && strcmp(op1,"1")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            if (strcmp(op,"||")==0 && strcmp(op2,"1")==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            if (strcmp(op,"||")==0 && strcmp(op1,op2)==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = %s\n",line_num,result,op1); continue; }
            if (strcmp(op,"==")==0 && strcmp(op1,op2)==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = 1\n",line_num,result); continue; }
            if (strcmp(op,"==")==0 && isNumericConstant(op1) && isNumericConstant(op2)){
                int r = (atof(op1) == atof(op2));
                g_bool_simp++; sprintf(imcode[i],"%d %s = %d\n",line_num,result,r); continue; }
            if (strcmp(op,"!=")==0 && strcmp(op1,op2)==0){
                g_bool_simp++; sprintf(imcode[i],"%d %s = 0\n",line_num,result); continue; }
            if (strcmp(op,"!=")==0 && isNumericConstant(op1) && isNumericConstant(op2)){
                int r = (atof(op1) != atof(op2));
                g_bool_simp++; sprintf(imcode[i],"%d %s = %d\n",line_num,result,r); continue; }
        }
    }
}


void conservativeJumpChaining() {
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
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000];
        strcpy(line, imcode[i]);
        char* if_ptr   = strstr(line, "if");
        char* goto_ptr = strstr(line, "goto");
        if (!goto_ptr) continue;
        if (if_ptr && if_ptr < goto_ptr) continue; 
        int line_num, target;
        if (sscanf(line, "%d goto %d", &line_num, &target) != 2) continue;
        int final_target = target;
        int steps = 0;
        while (steps++ < 1000) {
            if (final_target < 0 || final_target >= code) break;
            if (strstr(imcode[final_target], "// DEAD") != NULL) break;
            if (ref_count[final_target] != 1) break;
            char mid[10000];
            strcpy(mid, imcode[final_target]);
            char* mid_if   = strstr(mid, "if");
            char* mid_goto = strstr(mid, "goto");
            if (!mid_goto) break;
            if (mid_if && mid_if < mid_goto) break; 
            int mid_num, next_target;
            if (sscanf(mid, "%d goto %d", &mid_num, &next_target) != 2) break;
            ref_count[final_target]--;
            ref_count[next_target]++;
            final_target = next_target;
        }
        if (final_target != target) {
            g_jump_chain++;
            sprintf(imcode[i], "%d goto %d\n", line_num, final_target);
        }
    }
}


void redundantJumpElimination() {
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
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char* goto_ptr = strstr(imcode[i], "goto");
        if (!goto_ptr) continue;
        char* tp = goto_ptr + 4;
        while (*tp == ' ' || *tp == '\t') tp++;
        if (!isdigit(*tp)) continue;
        int target = atoi(tp);
        char* if_ptr = strstr(imcode[i], " if ");
        int is_conditional = (if_ptr != NULL && if_ptr < goto_ptr);
        if (i + 1 >= code) continue;
        int target_idx = -1;
        for (int j = i + 1; j < code; j++) {
            int jlnum = -1;
            sscanf(imcode[j], "%d", &jlnum);
            if (jlnum == target) { target_idx = j; break; }
        }
        if (target_idx == -1) continue;
        int all_dead_between = 1;
        for (int j = i + 1; j < target_idx; j++) {
            if (strstr(imcode[j], "// DEAD") == NULL) { all_dead_between = 0; break; }
        }
        if (!all_dead_between) continue;
        if (is_conditional) {
            int lnum; sscanf(imcode[i], "%d", &lnum);
            char original[10000]; strcpy(original, imcode[i]);
            char* space_ptr = strchr(original, ' ');
            if (space_ptr) {
                space_ptr++;
                g_dead_branch++;
                sprintf(imcode[i], "%d // DEAD BRANCH: %s", lnum, space_ptr);
            }
            continue;
        }
        if (ref_count[target] >= 2) {
            int lnum; sscanf(imcode[i], "%d", &lnum);
            char original[10000]; strcpy(original, imcode[i]);
            char* space_ptr = strchr(original, ' ');
            if (space_ptr) {
                space_ptr++;
                g_redund_jump++;
                sprintf(imcode[i], "%d // DEAD CODE: %s", lnum, space_ptr);
            }
        }
    }
}


void write_symtab_json(void) {
    FILE* fp = fopen("symtab.json", "w");
    if (!fp) return;
    int grand_vars  = 0;
    int grand_bytes = 0;
    fprintf(fp, "{\n  \"scopes\": [\n");
    for (int i = 0; i < env_count; i++) {
        Symbol* syms[MAX_SYMS];
        int n = collect_symbols(envs[i]->table, syms);
        char scope_label[50];
        if (i == 0) strcpy(scope_label, "Global");
        else        sprintf(scope_label, "Local (scope %d)", i);
        fprintf(fp, "    {\n");
        fprintf(fp, "      \"scope_id\": %d,\n", i);
        fprintf(fp, "      \"label\": \"%s\",\n", scope_label);
        fprintf(fp, "      \"prev_offset\": %d,\n", envs[i]->prev_offset);
        fprintf(fp, "      \"symbols\": [\n");
        for (int s = 0; s < n; s++) {
            Symbol* sym = syms[s];
            char base[100];
            extract_base(sym->type, base);
            int elem_size   = type_byte_size(base);
            int total_elems = 1;
            for (int d = 0; d < sym->dim_count; d++)
                total_elems *= sym->dimensions[d];
            int total_bytes = elem_size * (total_elems > 0 ? total_elems : 1);
            char dim_str[100] = "";
            if (sym->dim_count > 0) {
                for (int d = 0; d < sym->dim_count; d++) {
                    char part[20];
                    sprintf(part, "[%d]", sym->dimensions[d]);
                    strcat(dim_str, part);
                }
            } else if (strchr(sym->type, '[') != NULL) {
                char* p = strchr(sym->type, '[');
                strcpy(dim_str, p ? p : "");
            }
            char category[20];
            if      (sym->dim_count > 1)           strcpy(category, "multi-dim array");
            else if (sym->dim_count == 1)           strcpy(category, "array");
            else if (strchr(sym->type,'[') != NULL) strcpy(category, "array");
            else                                    strcpy(category, "scalar");
            char full_type[100];
            snprintf(full_type, sizeof(full_type), "%s%s", base, dim_str);
            char dims_json[200] = "[";
            if (sym->dim_count > 0) {
                for (int d = 0; d < sym->dim_count; d++) {
                    char tmp[20];
                    sprintf(tmp, "%d", sym->dimensions[d]);
                    strcat(dims_json, tmp);
                    if (d < sym->dim_count - 1) strcat(dims_json, ", ");
                }
            }
            strcat(dims_json, "]");
            fprintf(fp,
                "        {\n"
                "          \"name\": \"%s\",\n"
                "          \"type\": \"%s\",\n"
                "          \"base_type\": \"%s\",\n"
                "          \"offset\": %d,\n"
                "          \"elem_size\": %d,\n"
                "          \"total_bytes\": %d,\n"
                "          \"dim_count\": %d,\n"
                "          \"dimensions\": %s,\n"
                "          \"category\": \"%s\"\n"
                "        }%s\n",
                sym->name,
                full_type,
                base,
                sym->offset,
                elem_size,
                total_bytes,
                sym->dim_count,
                dims_json,
                category,
                (s < n - 1) ? "," : ""
            );
            grand_vars  += 1;
            grand_bytes += total_bytes;
        }
        fprintf(fp, "      ]\n");   /* end symbols array */
        fprintf(fp, "    }%s\n", (i < env_count - 1) ? "," : "");
    }
    fprintf(fp, "  ],\n");   /* end scopes array */
    fprintf(fp, "  \"summary\": {\n");
    fprintf(fp, "    \"total_scopes\": %d,\n", env_count);
    fprintf(fp, "    \"total_symbols\": %d,\n", grand_vars);
    fprintf(fp, "    \"total_storage_bytes\": %d\n", grand_bytes);
    fprintf(fp, "  }\n");
    fprintf(fp, "}\n");
    fclose(fp);
}

void finalRedundantGotoElimination() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char* goto_ptr = strstr(imcode[i], "goto");
        if (!goto_ptr) continue;
        char* if_ptr = strstr(imcode[i], " if ");
        if (if_ptr && if_ptr < goto_ptr) continue;
        char* tp = goto_ptr + 4;
        while (*tp == ' ' || *tp == '\t') tp++;
        if (!isdigit(*tp)) continue;
        int target = atoi(tp); 
        if (i + 1 >= code) continue;
        int target_idx = -1;
        for (int j = i + 1; j < code; j++) {
            int jlnum = -1;
            sscanf(imcode[j], "%d", &jlnum);
            if (jlnum == target) { target_idx = j; break; }
        }
        if (target_idx == -1) continue;   
        int all_dead_between = 1;
        for (int j = i + 1; j < target_idx; j++) {
            if (strstr(imcode[j], "// DEAD") == NULL) { all_dead_between = 0; break; }
        }
        if (!all_dead_between) continue;
        int lnum; sscanf(imcode[i], "%d", &lnum);
        char original[10000]; strcpy(original, imcode[i]);
        char* space_ptr = strchr(original, ' ');
        if (space_ptr) {
            space_ptr++;
            g_redund_jump++;
            sprintf(imcode[i], "%d // DEAD CODE: %s", lnum, space_ptr);
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
                    g_const_fold_arith++;
                    if (is_float) sprintf(imcode[i], "%d %s = %g\n", line_num, result, res);
                    else sprintf(imcode[i], "%d %s = %d\n", line_num, result, (int)res);
                }
            }
        }
    }
}
void warnUnusedVariables(void) {
    for (int sc = 0; sc < env_count; sc++) {
        Table* tbl = envs[sc]->table;
        for (int b = 0; b < tbl->size; b++) {
            TableEntry* entry = tbl->buckets[b];
            while (entry) {
                Symbol* sym = entry->value;
                const char* sname = sym->name;
                int slen = (int)strlen(sname);
                if (sname[0] == 't' && isdigit((unsigned char)sname[1])) {
                    entry = entry->next; continue;
                }
                if (strcmp(sym->type, "const int") == 0) {
                    entry = entry->next; continue;
                }
                for (int i = 0; i < code; i++) {
                    char kw[64], arg[256];
                    if (sscanf(imcode[i], "%*d %63s %255s", kw, arg) == 2 &&
                        strcmp(kw, "PopParam") == 0 &&
                        strcmp(arg, sname) == 0) {
                        goto next_sym;
                    }
                }
                {
                    int def_found = 0;
                    for (int i = 0; i < code; i++) {
                        char lhs[256];
                        if (sscanf(imcode[i], "%*d %255s =", lhs) == 1) {
                            char* br = strchr(lhs, '['); if (br) *br = '\0';
                            if (strcmp(lhs, sname) == 0) { def_found = 1; break; }
                        }
                    }
                    if (!def_found) { entry = entry->next; continue; }
                }
                {
                int used = 0;
                for (int i = 0; i < code && !used; i++) {
                    char* p = imcode[i];
                    while (*p == ' ') p++;
                    while (*p && isdigit((unsigned char)*p)) p++;
                    while (*p == ' ') p++;
                    if (strncmp(p, "PopParam",  8) == 0 ||
                        strncmp(p, "BeginFunc", 9) == 0 ||
                        strncmp(p, "EndFunc",   7) == 0)  continue;
                    const char* scan_start;
                    char* eq = NULL;
                    for (char* c = p; *c; c++) {
                        if (*c == '=') {
                            char prev = (c > p) ? *(c - 1) : ' ';
                            char next = *(c + 1);
                            /* skip  >=  <=  !=  ==  */
                            if (prev == '>' || prev == '<' ||
                                prev == '!' || prev == '=' || next == '=')
                                continue;
                            eq = c;
                            break;   
                        }
                    }
                    scan_start = eq ? (eq + 1) : p;
                    const char* pos = strstr(scan_start, sname);
                    while (pos) {
                        char before = (pos == scan_start) ? ' ' : *(pos - 1);
                        char after  = *(pos + slen);
                        if (!isalnum((unsigned char)before) && before != '_' &&
                            !isalnum((unsigned char)after)  && after  != '_') {
                            used = 1; break;
                        }
                        pos = strstr(pos + 1, sname);
                    }
                }
                if (!used) {
                    sprintf(err + strlen(err),
                        "Line %d: Warning: Variable '%s' is declared but never used\n",
                        sym->decl_line, sname);
                }
                }
                next_sym:
                entry = entry->next;
            }
        }
    }
}

void warnUnreachableCode(void) {
    int in_dead_block = 0;
    int block_start_src = -1;  
    for (int i = 0; i < code; i++) {
        if (imcode[i][0] == '\0') { in_dead_block = 0; continue; }
        if (strstr(imcode[i], "BeginFunc") != NULL ||
            strstr(imcode[i], "EndFunc")   != NULL) {
            in_dead_block = 0; continue;
        }
        int is_dead = (strstr(imcode[i], "// DEAD CODE:") != NULL);
        if (is_dead) {
            if (!in_dead_block) {
                sscanf(imcode[i], "%d", &block_start_src);
                in_dead_block = 1;
            }
        } else {
            if (in_dead_block) {
                sprintf(err + strlen(err),
                    "Line %d: Warning: Unreachable code detected (dead block starts here)\n",
                    block_start_src);
                in_dead_block = 0;
            }
        }
    }
    if (in_dead_block) {
        sprintf(err + strlen(err),
            "Line %d: Warning: Unreachable code detected (dead block starts here)\n",
            block_start_src);
    }
}

void deadVariableElimination() {
    int used[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        {
            char after_lnum[10000];
            const char* alnp = line + strspn(line, "0123456789 ");
            if (strncmp(alnp, "deref ", 6) == 0) {
                char pvar[100]; int pi = 0;
                const char* pp = alnp + 6;
                while (*pp && (isalnum((unsigned char)*pp) || *pp=='_')) pvar[pi++] = *pp++;
                pvar[pi] = '\0';
                if (pi > 0) {
                    for (int j = 0; j < code; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char clhs[100];
                        if (sscanf(imcode[j], "%*d %s =", clhs)==1 && strcmp(clhs,pvar)==0)
                            used[j] = 1;
                    }
                }
                const char* eq = strchr(alnp, '=');
                if (eq) {
                    const char* sv = eq + 1;
                    while (*sv == ' ') sv++;
                    char svar[100]; int si2 = 0;
                    while (*sv && (isalnum((unsigned char)*sv)||*sv=='_')) svar[si2++] = *sv++;
                    svar[si2] = '\0';
                    if (si2 > 0) {
                        for (int j = 0; j < code; j++) {
                            if (strstr(imcode[j], "// DEAD") != NULL) continue;
                            char clhs[100];
                            if (sscanf(imcode[j], "%*d %s =", clhs)==1 && strcmp(clhs,svar)==0)
                                used[j] = 1;
                        }
                    }
                }
            } else {
                const char* eq = strchr(alnp, '=');
                if (eq) {
                    const char* rv = eq + 1;
                    while (*rv == ' ') rv++;
                    if (strncmp(rv, "deref ", 6) == 0 || strncmp(rv, "ref ", 4) == 0) {
                        const char* pstart = rv + (strncmp(rv,"deref ",6)==0 ? 6 : 4);
                        char pvar2[100]; int pi2 = 0;
                        while (*pstart && (isalnum((unsigned char)*pstart)||*pstart=='_'))
                            pvar2[pi2++] = *pstart++;
                        pvar2[pi2] = '\0';
                        if (pi2 > 0) {
                            for (int j = 0; j < code; j++) {
                                if (strstr(imcode[j], "// DEAD") != NULL) continue;
                                char clhs[100];
                                if (sscanf(imcode[j], "%*d %s =", clhs)==1 && strcmp(clhs,pvar2)==0)
                                    used[j] = 1;
                            }
                        }
                    }
                }
            }
            (void)after_lnum;
        }
        {
            const char* alnp = line + strspn(line, "0123456789 ");
            if (strncmp(alnp, "FREE ", 5) == 0) {
                char fvar[100]; int fi = 0;
                const char* fp = alnp + 5;
                while (*fp && (isalnum((unsigned char)*fp) || *fp == '_')) fvar[fi++] = *fp++;
                fvar[fi] = '\0';
                if (fi > 0) {
                    for (int j = 0; j < code; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char clhs[100];
                        if (sscanf(imcode[j], "%*d %s =", clhs) == 1 && strcmp(clhs, fvar) == 0)
                            used[j] = 1;
                    }
                }
            }
        }
        /*  scan tokens for if/print/call/input lines, skipping string literals ── */
        if (strstr(line,"print")!=NULL||strstr(line,"Return")!=NULL||strstr(line,"PushParam")!=NULL||
            strstr(line,"Call")!=NULL||strstr(line,"if")!=NULL||
            strstr(line,"inputint")!=NULL||strstr(line,"inputfloat")!=NULL||strstr(line,"inputchar")!=NULL) {
            char* ptr = line;
            int in_str = 0;                          /*  string-literal guard */
            while (*ptr) {
                if (*ptr == '"') { in_str = !in_str; ptr++; continue; }   /* toggle on quote */
                if (in_str)      { ptr++; continue; }                      /* skip literal chars */
                if (isalpha((unsigned char)*ptr) || *ptr == '_') {
                    char var[100]; int idx = 0;
                    while (isalnum((unsigned char)*ptr) || *ptr == '_') var[idx++] = *ptr++;
                    var[idx] = '\0';
                    if (strcmp(var,"if")==0||strcmp(var,"goto")==0||strcmp(var,"print")==0||
                        strcmp(var,"printint")==0||strcmp(var,"printfloat")==0||strcmp(var,"printchar")==0||
                        strcmp(var,"printstring")==0||strcmp(var,"Return")==0||strcmp(var,"Call")==0||
                        strcmp(var,"PushParam")==0||strcmp(var,"PopParam")==0||strcmp(var,"BeginFunc")==0||
                        strcmp(var,"EndFunc")==0||strcmp(var,"inputint")==0||strcmp(var,"inputfloat")==0||
                        strcmp(var,"inputchar")==0||strcmp(var,"ref")==0||strcmp(var,"deref")==0) continue;
                    for (int j = 0; j < code; j++) {
                        if (strstr(imcode[j], "// DEAD") != NULL) continue;
                        char check_line[10000]; strcpy(check_line, imcode[j]);
                        char lhs[100];
                        if (sscanf(check_line, "%*d %s =", lhs) == 1) { if (strcmp(lhs, var) == 0) used[j] = 1; }
                    }
                } else ptr++;
            }
        }
        /*  scan index variable inside arr[idx] on LHS, skipping string literals ── */
        char lhs_full[100];
        if (sscanf(line, "%*d %[^=]", lhs_full) == 1) {
            char* bracket_start = strchr(lhs_full, '[');
            if (bracket_start) {
                char* bracket_end = strchr(bracket_start, ']');
                if (bracket_end) {
                    char* ptr = bracket_start + 1;
                    int in_str = 0;                  /* <-- NEW: string-literal guard */
                    while (ptr < bracket_end) {
                        if (*ptr == '"') { in_str = !in_str; ptr++; continue; }
                        if (in_str)     { ptr++; continue; }
                        if (isalpha((unsigned char)*ptr) || *ptr == '_') {
                            char var[100]; int idx = 0;
                            while ((isalnum((unsigned char)*ptr) || *ptr == '_') && ptr < bracket_end) var[idx++] = *ptr++;
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
        /* scan RHS tokens of regular assignments, skipping string literals ── */
        char lhs[100];
        if (sscanf(line, "%*d %s =", lhs) == 1) {
            char* equals = strchr(line, '=');
            if (equals) {
                char* rhs = equals + 1;
                char* ptr = rhs;
                int in_str = 0;                      /* <-- NEW: string-literal guard */
                while (*ptr) {
                    if (*ptr == '"') { in_str = !in_str; ptr++; continue; }
                    if (in_str)     { ptr++; continue; }
                    if (isalpha((unsigned char)*ptr) || *ptr == '_') {
                        char var[100]; int idx = 0;
                        while (isalnum((unsigned char)*ptr) || *ptr == '_') var[idx++] = *ptr++;
                        var[idx] = '\0';
                        if (strcmp(var,"Call")==0||strcmp(var,"PopParam")==0||strcmp(var,"int")==0||
                            strcmp(var,"float")==0||strcmp(var,"char")==0||strcmp(var,"double")==0||
                            strcmp(var,"long")==0||strcmp(var,"short")==0||
                            strcmp(var,"ref")==0||strcmp(var,"deref")==0) continue;
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
    int inputio_line[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
        if (strstr(imcode[i], "inputint")   != NULL ||
            strstr(imcode[i], "inputfloat") != NULL ||
            strstr(imcode[i], "inputchar")  != NULL) {
            char iline[10000]; strcpy(iline, imcode[i]);
            char keyword[50], varname[100];
            if (sscanf(iline, "%*d %s %s", keyword, varname) == 2) {
                for (int j = 0; j < code; j++) {
                    if (strstr(imcode[j], "// DEAD") != NULL) continue;
                    char clhs[100];
                    if (sscanf(imcode[j], "%*d %s =", clhs) == 1)
                        if (strcmp(clhs, varname) == 0) inputio_line[j] = 1;
                }
            }
        }
    }
    for (int i = 0; i < code; i++) {
        if (used[i] == 0 && strstr(imcode[i], "// DEAD") == NULL) {
            char line[10000]; strcpy(line, imcode[i]);
            char* eq = strchr(line, '=');
            if (!eq) continue;
            if (strstr(line,"BeginFunc") != NULL || strstr(line,"EndFunc")   != NULL ||
                strstr(line,"PopParam")  != NULL || strstr(line,"Call")      != NULL ||
                strstr(line,"printint")  != NULL || strstr(line,"printfloat")!= NULL ||
                strstr(line,"printchar") != NULL || strstr(line,"printstring")!=NULL ||
                strstr(line,"inputint")  != NULL || strstr(line,"inputfloat")!= NULL ||
                strstr(line,"inputchar") != NULL || strstr(line,"Return")    != NULL ||
                strstr(line,"goto")      != NULL || strstr(line," if ")      != NULL ||
                strstr(line,"PushParam") != NULL) continue;
            if (strstr(line," ref ")   != NULL) continue;
            {
                const char* alnp = line + strspn(line, "0123456789 ");
                if (strncmp(alnp, "deref ", 6) == 0) continue;
            }
            if (strstr(line, "ALLOC")   != NULL) continue;
            if (strstr(line, "CALLOC")  != NULL) continue;
            if (strstr(line, "REALLOC") != NULL) continue;
            char lhs[100];
            if (sscanf(line, "%*d %s", lhs) != 1) continue;
            char* br = strchr(lhs, '['); if (br) *br = '\0';
            char expected[200];
            snprintf(expected, sizeof(expected), "%s =", lhs);
            if (strstr(line, expected) == NULL) continue;
            if (inputio_line[i]) continue;
            {
                int enclosing_begin = -1;
                for (int k = i - 1; k >= 0; k--) {
                    if (strstr(imcode[k], "BeginFunc") != NULL) {
                        enclosing_begin = k;
                        break;
                    }
                }
                if (enclosing_begin >= 0 && is_ref_param(enclosing_begin, lhs))
                    continue;
            }
            char* content = strchr(line, ' ');
            if (content) { content++; g_dead_var++; sprintf(imcode[i], "%d // DEAD VAR: %s", i, content); }
        }
    }
}




void eliminateDeadCode() { 
    int is_jump_target[10000] = {0};
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;   
        if (strstr(imcode[i], "goto") != NULL) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) { int target = atoi(ptr); if (target >= 0 && target < code) is_jump_target[target] = 1; }
        }
    }
    int changed = 1;
    while (changed) {
        changed = 0;
        memset(is_jump_target, 0, sizeof(is_jump_target));
        for (int i = 0; i < code; i++) {
            if (strstr(imcode[i], "// DEAD") != NULL) continue;
            if (strstr(imcode[i], "goto") != NULL) {
                char* goto_ptr = strstr(imcode[i], "goto");
                char* ptr = goto_ptr + 4;
                while (*ptr == ' ' || *ptr == '\t') ptr++;
                if (isdigit(*ptr)) { int t = atoi(ptr); if (t >= 0 && t < code) is_jump_target[t] = 1; }
            }
        }
        for (int i = 0; i < code; i++) {
            if (strstr(imcode[i], "// DEAD") != NULL) continue;
            int is_uncond = 0;
            if (strstr(imcode[i], "Return") != NULL) is_uncond = 1;
            else if (strstr(imcode[i], "goto") != NULL) {
                char* if_ptr  = strstr(imcode[i], "if");
                char* goto_ptr = strstr(imcode[i], "goto");
                if (goto_ptr && (!if_ptr || if_ptr > goto_ptr)) is_uncond = 1;
            }
            if (!is_uncond) continue;
            for (int j = i + 1; j < code; j++) {
                if (strstr(imcode[j], "BeginFunc") != NULL) break;
                if (strstr(imcode[j], "EndFunc")   != NULL) break;
                if (is_jump_target[j]) break;           
                if (strstr(imcode[j], "// DEAD") != NULL) continue; 
                char original[10000]; strcpy(original, imcode[j]);
                char* sp = strchr(original, ' ');
                if (sp != NULL) { sp++; g_dead_code++; sprintf(imcode[j], "%d // DEAD CODE: %s", j, sp); }
                changed = 1;
            }
        }
    }
    int has_live_pred[10000] = {0};
    for (int i = 0; i < code; i++) { if (strstr(imcode[i],"BeginFunc")!=NULL && i+1<code) has_live_pred[i+1]=1; }
    has_live_pred[0] = 1;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i],"// DEAD CODE:")!=NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        if (strstr(imcode[i],"// DEAD")!=NULL) {
            if (i+1<code) has_live_pred[i+1]=1;
            char* gp = strstr(line,"goto");
            if (gp) {
                char* tp = gp+4; while (*tp==' '||*tp=='\t') tp++;
                if (isdigit((unsigned char)*tp)) {
                    int tgt = atoi(tp);
                    if (tgt>=0 && tgt<code) has_live_pred[tgt]=1;
                }
            }
            continue;
        }
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
            if (space_ptr!=NULL) { space_ptr++; g_dead_code++; sprintf(imcode[i], "%d // DEAD CODE: %s", i, space_ptr); }
        }
    }
}


void commonSubexpressionElimination() {
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) continue;
        char line[10000]; strcpy(line, imcode[i]);
        int line_num; char result[100], op1[100], op[10], op2[100];
        if (strstr(line, "ALLOC")   != NULL) continue;
        if (strstr(line, "CALLOC")  != NULL) continue;
        if (strstr(line, "REALLOC") != NULL) continue;
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
                    strstr(check_line,"PopParam")!=NULL||strstr(check_line,"PushParam")!=NULL||strstr(check_line,"Call")!=NULL) continue;
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
                    if (strcmp(op,check_op)==0 && strcmp(resolved_op1,resolved_check_op1)==0 && strcmp(resolved_op2,resolved_check_op2)==0) {
                        g_cse++;
                        sprintf(imcode[j], "%d %s = %s\n", check_line_num, check_result, result);
                    }
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
%token <str> ENUM ABS MIN MAX MODASN BREAK CONTINUE FOR DO IDEN NUM PASN MASN DASN SASN INC DEC LT GT LE GE NE OR AND EQ IF ELSE TR FL WHILE INT FLOAT CHAR CHARR
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
%token <str> ALLOC CALLOC REALLOC HFREE NULLPTR
%token <str> BAND BOR BXOR BNOT LSHIFT RSHIFT
%token <str> FUNCTION RETURN CALL
%type <expr> INIT_LIST
%type <decl> PARAMLIST
%type <expr> ARGLIST FUNCALL
%type <b> PROGRAM FUNDECL
%type <b>  CASE_LIST CASE_ITEM FORINCR
%type <expr> CASE_EXPR
%type <b> ENUM_MEMBER_LIST ENUM_MEMBER
%%
S:{top = create_env(top,0);} PROGRAM M MEOF{
//printf("\n%s\n", buffer);
//printf("^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n");
        if (e){    remove("unoptimized.tac");

                        printf("\nRejected \n%s \n",err);
                        err[0]='\0';buffer[0]='\0';}
                else {
                        backpatch($2->N,$3);
    remove("unoptimized.tac");
    FILE* tac_file1 = fopen("unoptimized.tac", "w");
    if (tac_file1) {
        for (int i = 0; i < code; i++)
            fprintf(tac_file1, "%s", imcode[i]);
        fclose(tac_file1);
    }         
        generateSymbolTableDOT();
        generateTACFlowDOT();
        generateTACFlowWithBlocks();
        generateCallGraphDOT();
        generateAllImages();
                        warnUnusedVariables();
 for (int pass = 0; pass < 15; pass++) {
    constantFolding();
    constantFoldConditionals();
    copyPropagation();
    algebraicSimplification();
    booleanSimplification();
    strengthReduction();
    commonSubexpressionElimination();
    peepholeOptimization();
    identityAssignmentElimination();
    deadStoreElimination();
    redundantLoadElimination();
   eliminateDeadCode();
    eliminateDeadCode();
    redundantJumpElimination();
    conservativeJumpChaining();
    eliminateDeadCode();
}
    inductionVariableElimination();
         loopInvariantCodeMotion();
deadVariableElimination();
int prev_dead_count = -1;
for (int dce_pass = 0; dce_pass < 15; dce_pass++) {
  eliminateDeadCode();
  deadVariableElimination();
   redundantJumpElimination();
    int dead_count = 0;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD CODE:") != NULL) dead_count++;
    }
    if (dead_count == prev_dead_count) break;
    prev_dead_count = dead_count;
}
finalRedundantGotoElimination();
generateOptimizationReport();
                        
                                             if (e) {
                            printf("\n=== Errors ===\n%s", err);
                            //printf("Rejected -> Bounds error detected after constant propagation. No output generated.\n");
                        } else {
                            if (strlen(err) > 0) {
                printf("\n=== Warnings ===\n%s", err);
            }
                        }
                }YYACCEPT;}
        | MEOF{YYACCEPT;}
| error MEOF{e=1;if(err[0]=='\0')sprintf(err,"Line %d: Invalid syntax or unexpected token\n", prev_lineno);

               printf("\nRejected -> %s \nCould not generate Three Address Code \n",err);
                YYACCEPT;};
PROGRAM: PROGRAM M FUNDECL {
            if(!e){
                backpatch($1->N, $2);
                $$ = createBoolNode();
                $$->N = $3->N;
                $$->B = $1->B;
                $$->C = $1->C;
            }
        }
        | PROGRAM M A {
            if(!e){
                backpatch($1->N, $2);
                $$ = createBoolNode();
                $$->N = $3->N;
                $$->B = merge($1->B, $3->B);
                $$->C = merge($1->C, $3->C);
            }
        }
        | FUNDECL {
            if(!e){
                $$ = createBoolNode();
                $$->N = $1->N;
            }
        }
        | A {$$ = $1;};

FUNDECL: FUNCTION TYPE IDEN '(' PARAMLIST ')' {
    if(!e){
        if(checkDuplicateParams($5)){
            e = 1;
            sprintf(err+strlen(err), "Line %d: Duplicate parameter names in function %s\n", yylineno, $3);
        }
       char clean_ret_type[100];
strcpy(clean_ret_type, $2->str);
if(clean_ret_type[0] == '@') memmove(clean_ret_type, clean_ret_type+1, strlen(clean_ret_type));
Function* f = createFunction($3, clean_ret_type);  
        f->start_label = code;
        struct Decl* p = $5;
        int pcount = 0;
        Param* param_tail = NULL;
        while(p){
            char clean_p_type[100];
            strcpy(clean_p_type, p->type);
            int param_is_ref = (clean_p_type[0] == '@');  
            if (clean_p_type[0] == '@') memmove(clean_p_type, clean_p_type+1, strlen(clean_p_type));
            Param* param = createParam(p->key, clean_p_type);
            param->is_ref = param_is_ref;  
            pcount++;
            if(f->params == NULL){ f->params = param; param_tail = param; }
            else { param_tail->next = param; param_tail = param; }
            p = p->next;
        }
        f->param_count = pcount;
        if(findFunction($3) != NULL){
            e=1;
            sprintf(err+strlen(err),"Line %d: Redeclaration of function %s\n", yylineno, $3);
        } else {
            addFunction(f);
        }
        sprintf(imcode[code], "%d BeginFunc %s %d\n", code, $3, pcount);
        code++;
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
            else if(strncmp(clean_param_type,"ptr:",4)==0) offset+=8; 
            else offset+=4;
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
    sprintf(err + strlen(err), "Line %d: Error: Non-void function '%s' must return a value of type %s\n",
            yylineno, current_function, current_return_type);
}
        sprintf(imcode[code], "%d EndFunc %s\n", code, $3);
        code++;
        $$ = createBoolNode();
        $$->N = $9->N;
        top = top->prev;
        if(!top) offset = 0;
        else offset = top->prev_offset;
        in_function = 0;
        current_function[0] = '\0';
        current_return_type[0] = '\0';
    }
};
PARAMLIST: TYPE IDEN ',' PARAMLIST {
            if(!e){
                $$ = createDecl($2);
                strcpy($$->type, $1->str);  
                $$->next = $4;
            }
        }
        | TYPE IDEN {
            if(!e){
                $$ = createDecl($2);
                strcpy($$->type, $1->str);  
            }
        }
        | {$$ = NULL;};

A:  SWITCH '(' EXPR ')' '{' { 
       if(!e) {
           strcpy(current_switch_var, $3->str);
                   top = create_env(top, offset);  
                  offset = 0;
                         char* base = getBaseType($3->type);
if(strstr($3->type, "[") != NULL) {
    e = 1;
    sprintf(err+strlen(err), "Line %d: Error: switch expression cannot be an array type '%s'\n", yylineno, $3->type);
} else if(!isIntegerType(base)) {
    e = 1;
    sprintf(err+strlen(err), "Line %d: Error: switch expression must be integer type, got '%s'\n", yylineno, base);
}
           switch_depth++;
       }
   } CASE_LIST '}' {
       if(!e) {
           $$ = createBoolNode();
           backpatch($7->N, code);
           backpatch($7->B, code);
                   top = top->prev;           
        offset = top->prev_offset;  
           switch_depth--;
       }
   }
| BREAK '$' {
    if (!e) {
        if(loop_depth == 0 && switch_depth == 0){
            e = 1;
            sprintf(err+strlen(err), "Line %d: break statement not within loop or switch\n", yylineno);
        }
        $$ = createBoolNode();
        $$->B = createNode(code);
        sprintf(imcode[code], "%d goto ", code);
        code++;
    }
}
| CONTINUE '$' {
    if (!e) {
        if(loop_depth == 0){
            e = 1;
            sprintf(err+strlen(err), "Line %d: continue statement not within a loop\n", yylineno);
        }
        $$ = createBoolNode();
        $$->C = createNode(code);
        sprintf(imcode[code], "%d goto ", code);
        code++;
    }
}
| RETURN EXPR '$' {
    if(!e){
        has_return_statement = 1;
        if(!in_function){
            e = 1;
            sprintf(err+strlen(err), "Line %d: Error: return statement outside function\n", yylineno);
        } else if(strcmp(current_return_type,"void")==0){
            e = 1;
            sprintf(err+strlen(err), "Line %d: Error: void function '%s' should not return a value\n", yylineno, current_function);
        } else if(!isTypeCompatible(current_return_type, $2->type)){
            e = 1;
            sprintf(err+strlen(err), "Line %d: Error: Return type mismatch in function '%s': expected %s, got %s\n", yylineno, current_function, current_return_type, $2->type);
        }
        if(!e){
         char ret_val[200];
        strcpy(ret_val, $2->str);
        char* ret_base = getBaseType(current_return_type);
        char* expr_base = getBaseType($2->type);
        if (strlen(ret_base) > 0 && strcmp(ret_base, expr_base) != 0
               && getTypeRank(ret_base) > 0 && getTypeRank(expr_base) > 0) {
            char* tmp = genvar();
            sprintf(imcode[code], "%d %s = (%s) %s\n", code, tmp, ret_base, $2->str);
            code++;
            strcpy(ret_val, tmp);
        }
                        sprintf(imcode[code], "%d Return %s\n", code, ret_val);
        code++;
        }
        $$ = createBoolNode();
    }
}
| RETURN '$' {
    if(!e){
        has_return_statement = 1;
        if(!in_function){
            e = 1;
            sprintf(err+strlen(err), "Line %d: Error: return statement outside function\n", yylineno);
        } else if(strcmp(current_return_type, "void") != 0) {
            e = 1;
            sprintf(err + strlen(err), "Line %d: Error: Non-void function '%s' must return a value of type %s\n", yylineno, current_function, current_return_type);
        }
        if(!e){
            sprintf(imcode[code], "%d Return\n", code);
            code++;
        }
        $$ = createBoolNode();
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
| CALL IDEN '(' ARGLIST ')' '$' {
    if(!e){
        Function* f = findFunction($2);
        if(f == NULL){
            e=1;
            sprintf(err+strlen(err), "Line %d: Function %s not declared\n", yylineno, $2);
        } else {
            struct Expr* arg = $4;
            int given = 0;
            while(arg){ given++; arg = arg->next; }
            if(given != f->param_count){
                e=1;
                sprintf(err+strlen(err), "Line %d: Function %s expects %d arguments, got %d\n", yylineno, $2, f->param_count, given);
            } else {
                arg = $4;
                Param* param = f->params;
                int arg_idx = 1;
                while(arg && param){
                    char* arg_base   = getBaseType(arg->type);
                    char* param_base = getBaseType(param->type);
                    char push_str[200];
                    strcpy(push_str, arg->str);
                    int is_ref = (arg->str[0] == '&');
                    int arg_is_ptr   = (strncmp(arg_base,   "ptr:", 4) == 0);
                    int param_is_ptr = (strncmp(param_base, "ptr:", 4) == 0);
                    if (!is_ref && (arg_is_ptr || param_is_ptr)) {
                        if (param_is_ptr && !arg_is_ptr) {
                            if (!(strcmp(arg->str,"0")==0 || strcmp(arg->str,"0.0")==0)) {
                                e = 1;
                                sprintf(err+strlen(err),
                                    "Line %d: Type error: argument %d of '%s' expects pointer type '%s', got non-pointer '%s'\n",
                                    yylineno, arg_idx, $2, param_base, arg_base);
                            }
                        } else if (arg_is_ptr && !param_is_ptr) {
                            e = 1;
                            sprintf(err+strlen(err),
                                "Line %d: Type error: argument %d of '%s' expects non-pointer type '%s', got pointer '%s'\n",
                                yylineno, arg_idx, $2, param_base, arg_base);
                        } else if (arg_is_ptr && param_is_ptr && strcmp(arg_base, param_base) != 0) {
                                                        e = 1;
                            sprintf(err+strlen(err),
                                "Line %d:  argument %d of '%s' passes '%s' where '%s' expected (pointer type mismatch)\n",
                                yylineno, arg_idx, $2, arg_base, param_base);
                        }
                    } else if(!is_ref &&
                       strcmp(arg_base, param_base) != 0 &&
                       getTypeRank(arg_base) > 0 && getTypeRank(param_base) > 0){
                        if(getTypeRank(arg_base) > getTypeRank(param_base)){
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Narrowing conversion from %s to %s for argument %d in call to '%s'\n",
                                yylineno, arg_base, param_base, arg_idx, $2);
                        }
                        if(isFloatingType(arg_base) && isIntegerType(param_base)){
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Conversion from %s to %s for argument %d in call to '%s' will discard fractional part\n",
                                yylineno, arg_base, param_base, arg_idx, $2);
                        }
                        if(isLiteral(arg->str)){
                            sprintf(push_str, "(%s)%s", param_base, arg->str);
                        } else {
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
            sprintf(err+strlen(err), "Line %d: Function %s not declared\n", yylineno, $2);
        } else {
            if(f->param_count != 0){
                e=1;
                sprintf(err+strlen(err), "Line %d: Function %s expects %d arguments, got 0\n", yylineno, $2, f->param_count);
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
        if(strcmp($3->type, "void") == 0){ 
            e = 1;
            sprintf(err+strlen(err), "Line %d: Error: cannot print a void expression\n", yylineno); 
        } else { 
            char* base_type = getBaseType($3->type);
            if(strstr($3->type, "char[") != NULL || strcmp($3->type, "char*") == 0 || strcmp(base_type, "ptr:char") == 0) 
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
}
|INPUT '(' EXPR ')' '$' { 
    if (!e) { 
        if(!$3->lv) { 
            e = 1;
            sprintf(err + strlen(err), "Line %d: Input requires a variable, not an expression\n", yylineno); 
        } else { 
            char* base_type = getBaseType($3->type);
            if(strstr($3->type, "char[") != NULL || strcmp($3->type, "char*") == 0 || strcmp(base_type, "ptr:char") == 0) 
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
}| ENUM { _enum_next_val = 0; } '{' ENUM_MEMBER_LIST '}' '$' {
    if (!e) {
        $$ = createBoolNode();
    }
}
| ASNEXPR '$' {if (!e){$$ = $1;}}
| ASNEXPR error MEOF{if(err[0]=='\0')sprintf(err,"Line %d: Missing dollar after assignment statement\n", prev_lineno);yyerrok;e=1;
                                                        printf("\nRejected -> %s -> Could not generate Three Address Code \n",err);
                                                        YYACCEPT;}
        | IF '(' BOOLEXPR ')' M  A {if (!e){
            backpatch($3->T, $5);
            $$ = createBoolNode();           
            int bonly = ($6->N == NULL && $6->C == NULL && $6->B != NULL);
            int conly = ($6->N == NULL && $6->B == NULL && $6->C != NULL);
            if ((bonly || conly)
                && $3->F != NULL && $3->F->addr != FALL_THROUGH
                && $3->T != NULL && $3->T->addr == FALL_THROUGH) {
                struct Node* exit_node = bonly ? $6->B : $6->C;
                if (exit_node != NULL && exit_node->addr == code - 1) {
                    imcode[code - 1][0] = 0;  
                    code--;                    
                    exit_node->addr = FALL_THROUGH; 
                }
                flipCondToTrue($3->F->addr);
                if (bonly) $$->B = $3->F;
                else       $$->C = $3->F;
                $$->N = NULL;
            } else {
                $$->N = merge($3->F, $6->N);
                $$->B = $6->B;
                $$->C = $6->C;
            }
        }}
        | IF '(' BOOLEXPR ')' M A ELSE NN M A {if (!e){
                backpatch($3->T,$5);
                backpatch($3->F,$9);
                $$ = createBoolNode();
                $$->N = merge(merge($6->N,$8->N),$10->N);
                $$->B = merge($6->B, $10->B);
                $$->C = merge($6->C, $10->C);
        }}
| EXPR error MEOF{{if(err[0]=='\0')sprintf(err,"Line %d: Missing dollar after expression statement\n", prev_lineno);yyerrok;e=1;}

                                                        printf("\nRejected -> %s -> Could not generate Three Address Code \n",err);
                                                        YYACCEPT;}
        | IF BOOLEXPR ')' M A ELSE NN M A{{sprintf(err+strlen(err),"Line %d: Missing opening parenthesis after 'if' keyword\n", yylineno);e=1;}}
        | WHILE M '(' BOOLEXPR ')' M {loop_depth++;} A {if (!e){
    loop_depth--;
    backpatch($8->N,$2);
    backpatch($8->C, $2);
    backpatch($4->T,$6);
    $$ = createBoolNode();
    $$->N = $4->F;
    sprintf(imcode[code],"%d goto %d\n",code,$2);
    code++;
    backpatch($8->B, code);
}}
        | WHILE M  BOOLEXPR ')' M A{{sprintf(err+strlen(err),"Line %d: Missing opening parenthesis after 'loop' keyword\n", yylineno);e=1;}}
        | DO M {loop_depth++;} A WHILE M '(' BOOLEXPR ')' '$' {
    if (!e) {
        loop_depth--;
        backpatch($4->N, $6);
        backpatch($4->C, $6);      
        flipCondToTrue($8->F->addr);
        backpatch($8->F, $2);      
        backpatch($4->B, code);     
        $$ = createBoolNode();
        $$->N = NULL;
    }
}
     | FOR '(' ASNEXPR '$' M BOOLEXPR
    {       
        $<addr>$ = code;   
    }
    '$' M FORINCR 
    {
        int incr_start = $<addr>7;   
        int incr_end   = code;       
        int incr_count = incr_end - incr_start;
        int sp = for_incr_sp++;
        for_incr_count[sp] = incr_count;
        for (int _i = 0; _i < incr_count; _i++)
            strcpy(for_incr_stash[sp][_i], imcode[incr_start + _i]);
        code = incr_start;
        $<addr>$ = incr_start;  
    }
  ')' M {loop_depth++;} A
    {
        if (!e) {
            loop_depth--;
            int cond_start  = $5;
            int incr_start  = $<addr>11;
            backpatch($15->N, code);
            backpatch($15->C, code);
            int stk = --for_incr_sp;
            int icnt = for_incr_count[stk];
            for (int _i = 0; _i < icnt; _i++) {
                int new_lnum = code + _i;
                char* src = for_incr_stash[stk][_i];
                char* spc = strchr(src, ' ');
                if (spc)
                    sprintf(imcode[code + _i], "%d%s", new_lnum, spc);
                else
                    strcpy(imcode[code + _i], src);
            }
            code += icnt;
            sprintf(imcode[code], "%d goto %d\n", code, cond_start);
            code++;
            backpatch($15->B, code);
            backpatch($6->F, code);
            $$ = createBoolNode();
            $$->N = NULL;
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
                if (decl_type[0] == '@') decl_type++;                  
                if (strcmp(s->type, decl_type) == 0){
                    sprintf(err + strlen(err), "Line %d: Redeclaration of %s\n", yylineno, s->name);
                } else {
                    sprintf(err + strlen(err), "Line %d: Conflicting types for %s\n", yylineno, s->name);
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
                sprintf(err+strlen(err), "Line %d: Cannot assign void expression to variable '%s'\n", yylineno, temp->key);
                break;  
            }
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
                    e = 1;
                    sprintf(err+strlen(err),
                        "Line %d: Warning: pointer type mismatch: initialising '%s' (type '%s') with value of type '%s'\n",
                        yylineno, temp->key, clean_type, temp->lt);
                }
            }
            if (e) break;  
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
                int init_count = 0;
                char* count_ptr = temp->op;
                while(*count_ptr){ if(*count_ptr==',') init_count++; count_ptr++; }
                if(strlen(temp->op)>0) init_count++;  
                if(init_count > temp->size){
                    e=1;
                    sprintf(err+strlen(err), "Line %d: Too many initializers for array %s (expected %d, got %d)\n", yylineno, temp->key, temp->size, init_count);
                }
                char check_copy[1000]; strcpy(check_copy, temp->op);
                char* check_token = strtok(check_copy, ",");
                int check_idx = 0;
             char fixed_op[1000]; fixed_op[0] = '\0';
                while(check_token != NULL){
                    while(*check_token == ' ') check_token++;
                    char* end = check_token + strlen(check_token) - 1;
                    while(end > check_token && *end == ' ') { *end = '\0'; end--; }
                    char current_val[50];
                    strcpy(current_val, check_token); 
                    if(isNumericConstant(check_token)){
                        double elem_val = atof(check_token);
                        if(strcmp(base_type,"char")==0 && (elem_val < -128 || elem_val > 127)){
                            int wrapped = (int)elem_val & 0xFF;
                            if(wrapped > 127) wrapped -= 256;
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Array element %.0f at index %d out of range for char [-128, 127] in '%s' (will wrap to %d)\n",
                                yylineno, elem_val, check_idx, temp->key, wrapped);
                            sprintf(current_val, "%d", wrapped);
                        }
                        else if(strcmp(base_type,"short")==0 && (elem_val < -32768 || elem_val > 32767)){
                            int wrapped = (int)elem_val & 0xFFFF;
                            if(wrapped > 32767) wrapped -= 65536;
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Array element %.0f at index %d out of range for short [-32768, 32767] in '%s' (will wrap to %d)\n",
                                yylineno, elem_val, check_idx, temp->key, wrapped);
                            sprintf(current_val, "%d", wrapped);
                        }
                        else if(strcmp(base_type,"int")==0 && (elem_val < -2147483648.0 || elem_val > 2147483647.0)){
                            long long wrapped = (long long)elem_val & 0xFFFFFFFF;
                            if(wrapped > 2147483647LL) wrapped -= 4294967296LL;
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Array element %.0f at index %d out of range for int in '%s' (will wrap to %lld)\n",
                                yylineno, elem_val, check_idx, temp->key, wrapped);
                            sprintf(current_val, "%lld", wrapped);
                        }
                        else if(strcmp(base_type,"float")==0){
                            if(elem_val > FLT_MAX || elem_val < -FLT_MAX){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Array element %g at index %d overflows float in '%s' (will be inf)\n",
                                    yylineno, elem_val, check_idx, temp->key);
                                sprintf(current_val, "inf");
                            }
                            else if(elem_val != 0.0 && fabs(elem_val) < FLT_MIN){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Array element %g at index %d underflows float in '%s' (will be 0)\n",
                                    yylineno, elem_val, check_idx, temp->key);
                                sprintf(current_val, "0.0");
                            }
                        }
                        else if(strcmp(base_type,"double")==0){
                            if(isinf(elem_val) || elem_val > DBL_MAX || elem_val < -DBL_MAX){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Array element %g at index %d overflows double in '%s' (will be inf)\n",
                                    yylineno, elem_val, check_idx, temp->key);
                                sprintf(current_val, "inf");
                            }
                            else if(elem_val != 0.0 && fabs(elem_val) < DBL_MIN){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Array element %g at index %d underflows double in '%s' (will be 0)\n",
                                    yylineno, elem_val, check_idx, temp->key);
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
                int string_len = temp->str_len;
                int array_size = temp->size;
                if (string_len > array_size) {
                    e = 1;
                    sprintf(err+strlen(err), "Line %d: Too many initializers: string literal requires %d bytes, but array '%s' has only %d bytes\n", yylineno, string_len, temp->key, array_size);
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
                char base_type[100]; strcpy(base_type, clean_type);
                char* actual_type = base_type;
                if(strncmp(base_type,"const ",6)==0) actual_type = base_type+6;
                char rhs_type[100]; strcpy(rhs_type, temp->lt);
                char* rhs_actual = rhs_type;
                if(strncmp(rhs_type,"const ",6)==0) rhs_actual = rhs_type+6;
                if(strcmp(actual_type, rhs_actual)==0){
                    sprintf(imcode[code],"%d %s = %s\n",code,temp->key,temp->op);
                    code++;
                }
                else {
                    if(temp->is_literal && isNumericConstant(temp->op)){
                        validateNumericLiteral(temp->op, actual_type, temp->key);
                        double val = atof(temp->op);
                        if(strcmp(actual_type,"char")==0){
                            if(val < -128 || val > 127){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Value %.0f out of range for char [-128, 127] in '%s' (will wrap to %d)\n",
                                    yylineno, val, temp->key, (char)(int)val);
                            }
                            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(char)(int)val);
                        }
                        else if(strcmp(actual_type,"short")==0){
                            if(val < -32768 || val > 32767){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Value %.0f out of range for short [-32768, 32767] in '%s' (will wrap to %d)\n",
                                    yylineno, val, temp->key, (short)(int)val);
                            }
                            sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(short)(int)val);
                        }                      
                        else if(strcmp(actual_type,"int")==0){
    if(val < -2147483648.0 || val > 2147483647.0){
        sprintf(err+strlen(err),
            "Line %d: Warning: Value %.0f out of range for int [-2147483648, 2147483647] in '%s' (will wrap to %d)\n",
            yylineno, val, temp->key, (int)(long long)val);
    }
    sprintf(imcode[code],"%d %s = %d\n",code,temp->key,(int)(long long)val);
}
                        else if(strcmp(actual_type,"long")==0){
    if(val > 9223372036854775807.0 || val < -9223372036854775808.0){
        sprintf(err+strlen(err),
            "Line %d: Warning: Value %.0f out of range for long in '%s' (will wrap)\n",
            yylineno, val, temp->key);
    }
    sprintf(imcode[code],"%d %s = %ld\n",code,temp->key,(long)(long long)val);
}
                        else if(strcmp(actual_type,"float")==0){
    float fval = (float)val;
    if(isinf(fval) && !isinf(val))
        sprintf(err+strlen(err),
            "Line %d: Warning: Value %g for '%s' overflows float (stored as inf)\n",
            yylineno, val, temp->key);
    sprintf(imcode[code],"%d %s = %g\n",code,temp->key,fval);
}
else if(strcmp(actual_type,"double")==0){
    sprintf(imcode[code],"%d %s = %g\n",code,temp->key,val);
}
                        else{
                            sprintf(imcode[code],"%d %s = (%s) %s\n",code,temp->key,actual_type,temp->op);
                        }
                        code++;
                    } else {
                        int target_rank = getTypeRank(actual_type);
                        int source_rank = getTypeRank(rhs_actual);                        
                        if(target_rank > 0 && source_rank > 0 && source_rank > target_rank){
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Narrowing conversion from %s to %s in '%s'\n",
                                yylineno, rhs_actual, actual_type, temp->key);
                        }                     
                        if(isFloatingType(rhs_actual) && isIntegerType(actual_type)){
                            sprintf(err+strlen(err),
                                "Line %d: Warning: Conversion from %s to %s will discard fractional part in '%s'\n",
                                yylineno, rhs_actual, actual_type, temp->key);
                        }                       
                        sprintf(imcode[code],"%d %s = (%s) %s\n",code,temp->key,actual_type,temp->op);
                        code++;
                    }
                }
            }
            temp = temp->next;
        }
}
| TYPE DECLLIST error MEOF{{if(err[0]=='\0')sprintf(err,"Line %d: Missing dollar after declaration\n", prev_lineno);yyerrok;e=1;}
                                                        printf("\nRejected -> %s -> Could not generate Three Address Code\n",err);
                                                        YYACCEPT; }
;
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
                sprintf(err+strlen(err), "Line %d: Duplicate enum constant '%s'\n", yylineno, $1);
            } else {
                int val = atoi($3);
                _enum_next_val = val + 1;   
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
                sprintf(err+strlen(err), "Line %d: Duplicate enum constant '%s'\n", yylineno, $1);
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
INDEX: '[' NUM ']' {$$ = createType();
                    int arr_size = atoi($2);
                    if(arr_size <= 0){
                        e=1;
                        sprintf(err+strlen(err), "Line %d: Array size must be positive (got %d)\n", yylineno, arr_size);
                    }
                    $$->size=arr_size;
                    sprintf($$->str,"array %d ", arr_size);
                    if (checkfloat($2)){
                            e=1;sprintf(err+strlen(err),"Line %d: Array index cannot be float\n", yylineno);
                    }}
        | '[' NUM ']' INDEX {$$ = createType();
                             int arr_size = atoi($2);
                             if(arr_size <= 0){
                                 e=1;
                                 sprintf(err+strlen(err), "Line %d: Array size must be positive (got %d)\n", yylineno, arr_size);
                             }
                             $$->size=$4->size*arr_size;
                             sprintf($$->str,"array %d %s", arr_size, $4->str);
                             if (checkfloat($2)){
                                     e=1;sprintf(err+strlen(err),"Line %d: Array index cannot be float\n", yylineno);
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
     | RSHIFTASN {strcpy($$,">>=");}   | MODASN {strcpy($$,"%=");} ;
BOOLEXPR:
         BOOLEXPR OR M BOOLEXPR {
             if (!e){
                 $$ = createBoolNode();
              
                 struct Node* b1_T = $1->T;
                 struct Node* b1_F = $1->F;

                 if (b1_T != NULL && b1_T->addr == FALL_THROUGH
                     && b1_F != NULL && b1_F->addr != FALL_THROUGH) {
                     if (flipCondToTrue(b1_F->addr)) {
                         b1_T = b1_F;   
                         b1_F = $1->T;  
                     }
                 }
                 backpatch(b1_F, $3);
                 $$->T = merge(b1_T, $4->T);
                 $$->F = $4->F;
             }}
    | BOOLEXPR AND M BOOLEXPR {
             if (!e){
                 backpatch($1->T,$3);
                 $$ = createBoolNode();
                 $$->T = $4->T;
                 $$->F = merge($1->F,$4->F);
             }}
        | '!' BOOLEXPR {
    if (!e){ 
        $$ = createBoolNode(); 
        $$->T = $2->F; 
        $$->F = $2->T;       
        if ($$->F != NULL && $$->F->addr == FALL_THROUGH && 
            $$->T != NULL && $$->T->addr != FALL_THROUGH) {
            if (flipCondToTrue($$->T->addr)) {
                struct Node* temp = $$->T;
                $$->T = $$->F;
                $$->F = temp;
            }
        }
    }
}
        | '(' BOOLEXPR ')' {
                if (!e){ $$ = createBoolNode(); $$->T = $2->T; $$->F = $2->F; }
        }
        | EXPR LT EXPR  {if(!e) {
               
                $$ = createBoolNode();
                sprintf(imcode[code],"%d if %s >= %s goto ",code,$1->str,$3->str);
                $$->F = createNode(code); code++;
                $$->T = createNode(FALL_THROUGH);
        }}
    | EXPR GT EXPR  {if(!e) {
                $$ = createBoolNode();
                sprintf(imcode[code],"%d if %s <= %s goto ",code,$1->str,$3->str);
                $$->F = createNode(code); code++;
                $$->T = createNode(FALL_THROUGH);
        }}
        | EXPR EQ EXPR  {if(!e) {
                $$ = createBoolNode();
                sprintf(imcode[code],"%d if %s != %s goto ",code,$1->str,$3->str);
                $$->F = createNode(code); code++;
                $$->T = createNode(FALL_THROUGH);
        }}
    | EXPR NE EXPR  {if(!e) {
                $$ = createBoolNode();
                sprintf(imcode[code],"%d if %s == %s goto ",code,$1->str,$3->str);
                $$->F = createNode(code); code++;
                $$->T = createNode(FALL_THROUGH);
        }}
        | EXPR LE EXPR  {if(!e) {
                $$ = createBoolNode();
                sprintf(imcode[code],"%d if %s > %s goto ",code,$1->str,$3->str);
                $$->F = createNode(code); code++;
                $$->T = createNode(FALL_THROUGH);
        }}
    | EXPR GE EXPR  {if(!e) {
                $$ = createBoolNode();
                sprintf(imcode[code],"%d if %s < %s goto ",code,$1->str,$3->str);
                $$->F = createNode(code); code++;
                $$->T = createNode(FALL_THROUGH);
        }}
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
            sprintf(err+strlen(err), "Line %d: Cannot assign void expression to '%s'\n", yylineno, $1->str);
        }
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
                                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: Warning: pointer type mismatch: assigning '%s' to '%s'\n",
                    yylineno, $3->type, $1->type);
            }
        }
        if ($1->is_deref && !e) {
            if (strlen($2) != 1 || $2[0] != '=') {
                e = 1;
                sprintf(err+strlen(err),
                    "Line %d: Compound assignment through pointer not supported; use simple '='\n",
                    yylineno);
            } else {
                sprintf(imcode[code], "%d deref %s = %s\n", code, $1->deref_src, $3->str);
                code++;
            }
            $$ = createBoolNode();
        } else {
        Symbol* sym = env_get(top, $1->str);
        if(sym && strstr(sym->type, "const") != NULL){
            e=1;
            sprintf(err+strlen(err), "Line %d: Cannot assign to const variable %s\n", yylineno, $1->str);
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
                    sprintf(err+strlen(err), "Line %d: String literal too large for array (needs %d bytes, array is %d bytes)\n", yylineno, string_len, array_size);
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
    char op_only[10];
    strncpy(op_only, $2, sizeof(op_only)-1);
    op_only[sizeof(op_only)-1] = '\0';
    int op_len = strlen(op_only);
    if (op_len > 0 && op_only[op_len-1] == '=') op_only[op_len-1] = '\0';
    Symbol* lhs_sym = env_get(top, $1->str);
    char lhs_type[100] = "";
    if(lhs_sym) strcpy(lhs_type, getBaseType(lhs_sym->type));
    char lhs_base[100], rhs_base[100];
    strcpy(lhs_base, lhs_type[0] ? lhs_type : $1->type);
    strcpy(rhs_base, getBaseType($3->type));
    char* promoted = promoteType(lhs_base, rhs_base);
    if((strcmp(op_only,"&")==0||strcmp(op_only,"|")==0||strcmp(op_only,"^")==0||
        strcmp(op_only,"<<")==0||strcmp(op_only,">>")==0) &&
       (isFloatingType(lhs_base)||isFloatingType(rhs_base))){
        e=1;
        sprintf(err+strlen(err), "Line %d: Error: Bitwise operator '%s=' cannot be applied to float/double types\n", yylineno, op_only);
    } else {
        char lhs_str[100]; strcpy(lhs_str, $1->str);
        if(strcmp(lhs_base, promoted) != 0){
            char* cl = genvar();
            sprintf(imcode[code],"%d %s = (%s) %s\n",code,cl,promoted,$1->str); code++;
            strcpy(lhs_str, cl);
        }
        char rhs_str[100]; strcpy(rhs_str, $3->str);
        if(strcmp(rhs_base, promoted) != 0){
            char* cr = genvar();
            sprintf(imcode[code],"%d %s = (%s) %s\n",code,cr,promoted,$3->str); code++;
            strcpy(rhs_str, cr);
        }
        sprintf(imcode[code],"%d %s = %s %s %s\n",code,t,lhs_str,op_only,rhs_str); code++;
        if(strcmp(lhs_base, promoted) != 0){
            sprintf(err+strlen(err),
                "Line %d: Warning: Implicit narrowing conversion from %s to %s in compound assignment to '%s'\n",
                yylineno, promoted, lhs_base, $1->str);
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
    if (!$1->lv){e=1;sprintf(err+strlen(err), "Line %d: L value not assignable\n", yylineno);}
}
FORINCR: ASNEXPR {
    if (!e) {
        $$ = $1;
    }
}
| EXPR {
    if (!e) {
        $$ = createBoolNode();
    }
}
;
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
        if(!found){ e=1; sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $3); }
        sprintf($$->str, "%d", var_size);
        strcpy($$->type, "int");
        $$->lv = 0;
    }
}
| SIZEOF '(' TYPE ')' {
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
| ALLOC '(' EXPR ')' {
    if(!e){
        $$ = createExpr();
        char* ret = genvar();
        sprintf(imcode[code], "%d %s = ALLOC 1 * %s\n", code, ret, $3->str);
        code++;
        strcpy($$->str, ret);
        strcpy($$->type, "ptr:void");
        $$->lv = 0;
    } else { $$ = createExpr(); }
}
| ALLOC '(' EXPR ',' TYPE ')' {
    if(!e){
        $$ = createExpr();
        char clean_t[100]; strcpy(clean_t, $5->str);
        if(clean_t[0]=='@') memmove(clean_t, clean_t+1, strlen(clean_t));
        int tsz = 4; /* default */
        if(strcmp(clean_t,"char")==0)   tsz=1;
        else if(strcmp(clean_t,"short")==0) tsz=2;
        else if(strcmp(clean_t,"int")==0||strcmp(clean_t,"float")==0) tsz=4;
        else if(strcmp(clean_t,"long")==0||strcmp(clean_t,"double")==0) tsz=8;
        else if(strncmp(clean_t,"ptr:",4)==0) tsz=8;
        char* ret = genvar();
        sprintf(imcode[code], "%d %s = ALLOC %d * %s\n", code, ret, tsz, $3->str);
        code++;
        char ptr_type[120]; sprintf(ptr_type, "ptr:%s", clean_t);
        strcpy($$->str, ret);
        strcpy($$->type, ptr_type);
        $$->lv = 0;
    } else { $$ = createExpr(); }
}
| CALLOC '(' EXPR ',' EXPR ')' {
    if(!e){
        $$ = createExpr();
        char* ret = genvar();
        sprintf(imcode[code], "%d %s = CALLOC %s, %s\n", code, ret, $3->str, $5->str);
        code++;
        strcpy($$->str, ret);
        strcpy($$->type, "ptr:void");
        $$->lv = 0;
    } else { $$ = createExpr(); }
}
| CALLOC '(' EXPR ',' TYPE ')' {
    if(!e){
        $$ = createExpr();
        char clean_t[100]; strcpy(clean_t, $5->str);
        if(clean_t[0]=='@') memmove(clean_t, clean_t+1, strlen(clean_t));
        int tsz = 4;
        if(strcmp(clean_t,"char")==0)   tsz=1;
        else if(strcmp(clean_t,"short")==0) tsz=2;
        else if(strcmp(clean_t,"int")==0||strcmp(clean_t,"float")==0) tsz=4;
        else if(strcmp(clean_t,"long")==0||strcmp(clean_t,"double")==0) tsz=8;
        else if(strncmp(clean_t,"ptr:",4)==0) tsz=8;
        char* ret = genvar();
        sprintf(imcode[code], "%d %s = CALLOC %s, %d\n", code, ret, $3->str, tsz);
        code++;
        char ptr_type[120]; sprintf(ptr_type, "ptr:%s", clean_t);
        strcpy($$->str, ret);
        strcpy($$->type, ptr_type);
        $$->lv = 0;
    } else { $$ = createExpr(); }
}
| REALLOC '(' IDEN ',' EXPR ')' {
    if(!e){
        $$ = createExpr();
        Env* tmp = top; int found=0; Symbol* psym=NULL;
        while(tmp){ psym=get(tmp->table,$3); if(psym){ found=1; break; } tmp=tmp->prev; }
        if(!found){ e=1; sprintf(err+strlen(err),"Line %d: '%s' is not declared in scope\n",yylineno,$3); }
        if(!e){
            int tsz = 1; 
            if(psym && strncmp(psym->type,"ptr:",4)==0){
                const char* pointee = psym->type + 4;
                if(strcmp(pointee,"char")==0)         tsz=1;
                else if(strcmp(pointee,"short")==0)   tsz=2;
                else if(strcmp(pointee,"int")==0||strcmp(pointee,"float")==0) tsz=4;
                else if(strcmp(pointee,"long")==0||strcmp(pointee,"double")==0) tsz=8;
                else if(strncmp(pointee,"ptr:",4)==0) tsz=8;
                else tsz=1; 
            }
            char* ret = genvar();
            if(tsz == 1){
                sprintf(imcode[code], "%d %s = REALLOC %s, %s\n", code, ret, $3, $5->str);
            } else {
                sprintf(imcode[code], "%d %s = REALLOC %s, %d * %s\n", code, ret, $3, tsz, $5->str);
            }
            code++;
            if(psym && strncmp(psym->type,"ptr:",4)==0)
                strcpy($$->type, psym->type);
            else
                strcpy($$->type, "ptr:void");
            strcpy($$->str, ret);
            $$->lv = 0;
        }
    } else { $$ = createExpr(); }
}
| NULLPTR {
    if(!e){
        $$ = createExpr();
        strcpy($$->str, "0");
        strcpy($$->type, "ptr:void");
        $$->lv = 0;
    } else { $$ = createExpr(); }
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
| MIN '(' ARGLIST ')' {
    if (!e) {
        $$ = createExpr();
        struct Expr* args = $3;
        if (args == NULL) {
            e = 1;
            sprintf(err + strlen(err), "Line %d: min() requires at least one argument\n", yylineno);
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
| MAX '(' ARGLIST ')' {
    if (!e) {
        $$ = createExpr();
        struct Expr* args = $3;
        if (args == NULL) {
            e = 1;
            sprintf(err + strlen(err), "Line %d: max() requires at least one argument\n", yylineno);
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
            int lptr = isPointerType($1->type);
            int rptr = isPointerType($3->type);
            if (lptr && !rptr) {
                char* t = genvar(); strcpy($$->str, t);
                strcpy($$->type, $1->type);
                sprintf(imcode[code],"%d %s = %s + %s\n",code,t,$1->str,$3->str); code++;
            } else if (!lptr && rptr) {
                char* t = genvar(); strcpy($$->str, t);
                strcpy($$->type, $3->type);
                sprintf(imcode[code],"%d %s = %s + %s\n",code,t,$1->str,$3->str); code++;
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
            int lptr = isPointerType($1->type);
            int rptr = isPointerType($3->type);
            if (lptr && !rptr) {
                char* t = genvar(); strcpy($$->str, t);
                strcpy($$->type, $1->type);
                sprintf(imcode[code],"%d %s = %s - %s\n",code,t,$1->str,$3->str); code++;
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
            e=1; sprintf(err+strlen(err), "Line %d: Division by zero\n", yylineno);
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
            e=1; sprintf(err+strlen(err), "Line %d: Modulo by zero\n", yylineno);
        }
        $$ = createExpr();
        if (tryConstantFold($1, $3, '%', $$)) {
        } else {
            if (isFloatingType($1->type) || isFloatingType($3->type)){
                e=1;
                sprintf(err+strlen(err), "Line %d: invalid operands to binary %% (float/double)\n", yylineno);
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
        | EXPR OP '$'{e=1;sprintf(err+strlen(err), "Line %d: Error: missing right-hand operand after operator\n", yylineno);yyerrok;}
    | EXPR BAND EXPR {
        if (!e){ 
            $$ = createExpr();
            if (tryConstantFold($1, $3, '&', $$)) { $$->lv = 0; } else {
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err), "Line %d: invalid operands to bitwise & (float/double)\n", yylineno); }
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
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err), "Line %d: invalid operands to bitwise | (float/double)\n", yylineno); }
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
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err), "Line %d: invalid operands to bitwise ^ (float/double)\n", yylineno); }
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
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err), "Line %d: invalid operands to << (float/double)\n", yylineno); }
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
                if (isFloatingType($1->type) || isFloatingType($3->type)){ e=1; sprintf(err+strlen(err), "Line %d: invalid operands to >> (float/double)\n", yylineno); }
                strcpy($$->type,$1->type);
                char* t = genvar(); strcpy($$->str,t);
                sprintf(imcode[code],"%d %s = %s >> %s\n",code,t,$1->str,$3->str); code++;
            }
            $$->lv=0;
        }
    }
    | BNOT EXPR {
    if (!e){
        if (isFloatingType($2->type)){ e=1; sprintf(err+strlen(err), "Line %d: invalid operand to bitwise ~ (float/double)\n", yylineno); }
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
        sprintf(imcode[code], "%d %s = 1\n", code, cond_var); code++;
        int C1 = code;
        sprintf(imcode[code], "%d goto %d\n", code, code + 2); code++;
        int C2 = code;
        sprintf(imcode[code], "%d %s = 0\n", code, cond_var); code++;
        backpatch($1->T, C0);
        backpatch($1->F, C2);
        int C3 = code;
        int C6 = code + 3;   
        sprintf(imcode[code], "%d if %s == 0 goto %d\n", code, cond_var, C6); code++;
        sprintf(imcode[code], "%d %s = %s\n", code, t, $3->str); code++;
        int C5 = code;
        int C7 = code + 2;   
        sprintf(imcode[code], "%d goto %d\n", code, C7); code++;
        sprintf(imcode[code], "%d %s = %s\n", code, t, $5->str); code++;
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
    }
}  
  | FUNCALL {$$ = $1;} 
    | TERM {$$ = $1;}
    | ADDROF IDEN {
        if (!e) {
            $$ = createExpr();
            Symbol* sym = env_get(top, $2);
            if (!sym) {
                e = 1;
                sprintf(err+strlen(err), "Line %d: '%s' not declared in scope\n", yylineno, $2);
                strcpy($$->str, "0");
                strcpy($$->type, "ptr:int");
            } else {
                char* t = genvar();
                sprintf(imcode[code], "%d %s = ref %s\n", code, t, $2);
                code++;
                strcpy($$->str, t);
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
                            int _is_null = (strcmp(_rhs, "0") == 0 || strcmp(_rhs, "0.0") == 0);
                            if (!_is_null) {
                                char* _sp = strrchr(_rhs, ' ');
                                if (_sp && (strcmp(_sp+1,"0")==0 || strcmp(_sp+1,"0.0")==0))
                                    _is_null = 1;
                            }
                            if (_is_null) {
                                e = 1;
                                _null_deref = 1;
                                sprintf(err+strlen(err),
                                    "Line %d: Error: dereferencing '%s' which is null \n",
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
            $$ = createExpr();
            if(!e){
                Function* f = findFunction($2);
                if(f == NULL){
                    e=1;
                    sprintf(err+strlen(err),"Line %d: Function %s not declared\n", yylineno, $2);
                } else {
                    int arg_count = 0;
                    struct Expr* arg = $4;
                    Param* param = f->params;
                    while(arg && param){
                        arg_count++;
                        char* a_base = getBaseType(arg->type);
                        char* p_base = getBaseType(param->type);
                        int a_is_ptr = (strncmp(a_base, "ptr:", 4) == 0);
                        int p_is_ptr = (strncmp(p_base, "ptr:", 4) == 0);
                        int a_is_ref = (arg->str[0] == '&');
                        if (!a_is_ref && (a_is_ptr || p_is_ptr)) {
                            if (p_is_ptr && !a_is_ptr) {
                                if (!(strcmp(arg->str,"0")==0 || strcmp(arg->str,"0.0")==0)) {
                                    e = 1;
                                    sprintf(err+strlen(err),
                                        "Line %d: Type error: argument %d of '%s' expects pointer type '%s', got non-pointer '%s'\n",
                                        yylineno, arg_count, $2, p_base, a_base);
                                }
                            } else if (a_is_ptr && !p_is_ptr) {
                                e = 1;
                                sprintf(err+strlen(err),
                                    "Line %d: Type error: argument %d of '%s' expects non-pointer type '%s', got pointer '%s'\n",
                                    yylineno, arg_count, $2, p_base, a_base);
                            }
                        } else if (!a_is_ref && !isTypeCompatible(param->type, arg->type)){
                            sprintf(err+strlen(err),"Line %d:  Argument %d type mismatch in call to %s: expected %s, got %s\n",
                                    yylineno, arg_count, $2, param->type, arg->type);
                        }
                        arg = arg->next;
                        param = param->next;
                    }
                    while(arg){ arg_count++; arg = arg->next; }
                    if(arg_count != f->param_count){
                        e=1;
                       sprintf(err + strlen(err),
        "Line %d: Function %s expects %d arguments, got %d\n",
        yylineno, $2, f->param_count, arg_count);
                        strcpy($$->type, f->return_type);
                        /* Do NOT fall through into code-gen — bail out now */
                        goto funcall_arglist_done;
                    }
                    {
                    struct Expr* reversed = NULL;
                    arg = $4;
                    Param* rparam = f->params;
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
                        int is_ref = (arg->str[0] == '&');
                        int arg_is_ptr   = (strncmp(arg_base,   "ptr:", 4) == 0);
                        int param_is_ptr = (strncmp(param_base, "ptr:", 4) == 0);
                        if (!is_ref && (arg_is_ptr || param_is_ptr)) {
                            if (param_is_ptr && !arg_is_ptr) {
                                if (!(strcmp(arg->str,"0")==0 || strcmp(arg->str,"0.0")==0)) {
                                    e = 1;
                                    sprintf(err+strlen(err),
                                        "Line %d: Type error: argument %d of '%s' expects pointer type '%s', got non-pointer '%s'\n",
                                        yylineno, rarg_idx, $2, param_base, arg_base);
                                }
                            } else if (arg_is_ptr && !param_is_ptr) {
                                e = 1;
                                sprintf(err+strlen(err),
                                    "Line %d: Type error: argument %d of '%s' expects non-pointer type '%s', got pointer '%s'\n",
                                    yylineno, rarg_idx, $2, param_base, arg_base);
                            } else if (arg_is_ptr && param_is_ptr && strcmp(arg_base, param_base) != 0) {
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: argument %d of '%s' passes '%s' where '%s' expected (pointer type mismatch)\n",
                                    yylineno, rarg_idx, $2, arg_base, param_base);
                            }
                        } else if(!is_ref &&
                           strcmp(arg_base, param_base) != 0 &&
                           getTypeRank(arg_base) > 0 && getTypeRank(param_base) > 0){
                            if(getTypeRank(arg_base) > getTypeRank(param_base)){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Narrowing conversion from %s to %s for argument %d in call to '%s'\n",
                                    yylineno, arg_base, param_base, rarg_idx, $2);
                            }
                            if(isFloatingType(arg_base) && isIntegerType(param_base)){
                                sprintf(err+strlen(err),
                                    "Line %d: Warning: Conversion from %s to %s for argument %d in call to '%s' will discard fractional part\n",
                                    yylineno, arg_base, param_base, rarg_idx, $2);
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
                        sprintf(err+strlen(err), "Line %d: Cannot use return value of void function '%s'\n", yylineno, $2);
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
                sprintf(err+strlen(err),"Line %d: Function %s not declared\n", yylineno, $2);
                } else {
                    if(f->param_count != 0){
                        e=1;
                       sprintf(err + strlen(err),
        "Line %d: Function %s expects %d arguments, got 0\n",
        yylineno, $2, f->param_count);
                    }
                    strcpy($$->type, f->return_type);
                    $$->lv = 0;
                    if(strcmp(f->return_type, "void") == 0) {
                        e = 1;
                        sprintf(err+strlen(err), "Line %d: Cannot use return value of void function '%s'\n", yylineno, $2);
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
                    sprintf(err+strlen(err), "Line %d: Pass-by-reference requires a variable (lvalue), not an expression\n", yylineno);
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
                    sprintf(err+strlen(err), "Line %d: Pass-by-reference requires a variable (lvalue), not an expression\n", yylineno);
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
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err), "Line %d: Cannot modify const variable %s\n", yylineno, $3); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $3); e=1; }
        sprintf(imcode[code],"%d %s = %s %c 1\n",code,$3,$3,$2[0]);code++;
strcpy($$->str,$3);
    } else {
        if (!strcmp($2,"--")){e=1;sprintf(err+strlen(err), "Line %d: '---' is not allowed (use unary minus on a decremented variable separately)\n", yylineno);}
        Env* temp = top; int found=0;
        while(temp){
            if (get(temp->table,$3)){
                found = 1;
                Symbol* t = get(temp->table,$3);
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err), "Line %d: Cannot modify const variable %s\n", yylineno, $3); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $3); e=1; }
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
        char*t = genvar();
sprintf(imcode[code],"%d %s = %s\n",code,t,$2);code++;
sprintf(imcode[code],"%d %s = %s %c 1\n",code,$2,$2,$3[0]);code++;
strcpy($$->str,t);
        Env* temp = top; int found=0;
        while(temp){
            if (get(temp->table,$2)){
                found = 1;
                Symbol* t = get(temp->table,$2);
                /*  const check on post-inc/dec */
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err), "Line %d: Cannot modify const variable %s\n", yylineno, $2); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $2); e=1; }
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
                if(strstr(t->type,"const")!=NULL){ e=1; sprintf(err+strlen(err), "Line %d: Cannot modify const variable %s\n", yylineno, $2); }
                strcpy($$->type,t->type);
                break;
            }
            temp = temp->prev;
        }
        if (!found){ sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $2); e=1; }
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
    if (!found){ sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $2); e=1; }
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
    if (!found){ sprintf(err+strlen(err), "Line %d: %s is not declared in scope\n", yylineno, $2); e=1; }
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
| UN INC NUM {e=1;sprintf(err+strlen(err), "Line %d: Error: cannot increment a constant value\n", yylineno);}
| UN DEC NUM {e=1;sprintf(err+strlen(err), "Line %d: Error: cannot decrement a constant value\n", yylineno);}
| UN NUM INC {e=1;sprintf(err+strlen(err), "Line %d: Error: cannot increment a constant value\n", yylineno);}
| UN NUM DEC {e=1;sprintf(err+strlen(err), "Line %d: Error: cannot decrement a constant value\n", yylineno);}
;
    OPR: INC {strcpy($$,$1);}| DEC {strcpy($$,$1);};
B : OPR {e=1;sprintf(err+strlen(err), "Line %d: Error: expression is not assignable\n", yylineno);}
  | IDEN {e=1;sprintf(err+strlen(err), "Line %d: Error: missing operator before identifier '%s'\n", yylineno, $1);}
  | NUM {e=1;sprintf(err+strlen(err), "Line %d: Error: missing operator before number\n", yylineno);}
  |;
C : IDEN {e=1;sprintf(err+strlen(err), "Line %d: Error: missing operator before identifier '%s'\n", yylineno, $1);}
  | NUM {e=1;sprintf(err+strlen(err), "Line %d: Error: missing operator before number\n", yylineno);}
  |;
UN : '-' {strcpy($$,"-");}  | '+' {strcpy($$,"+");} | {strcpy($$,"");} ;
%%
char* genvar(){
    char *re = (char*)malloc(sizeof(char)*100);
    sprintf(re,"t%d",label);
    label++;
    return re;
}int yyerror(char* msg){ 
    if(err_line == 0) err_line = yylineno;   
    e = 1;
    if(err[0] == '\0')
        sprintf(err, "Syntax error at line %d: %s\n", err_line, msg);
    return 0;
}



void printQuadruples() {
    printf("\n");
    printf("================================================================================\n");
    printf("                              QUADRUPLES TABLE                                  \n");
    printf("================================================================================\n");
    printf("  %-4s  %-18s  %-18s  %-18s  %-18s\n",
           "#", "op", "arg1", "arg2", "result");
    printf("  %-4s  %-18s  %-18s  %-18s  %-18s\n",
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
        /* skip digits */
        while (*p && (*p >= '0' && *p <= '9')) p++;
        while (*p == ' ') p++;

        /* ─── fields we will fill ─── */
        char op[100]="", arg1[200]="", arg2[200]="", result[200]="-";
        strcpy(arg2, "-");
        strcpy(result, "-");

        /* ── dead-code / comment lines ── */
        if (strncmp(p, "//", 2) == 0) {
            strcpy(op, p);
            strcpy(arg1, "-");
        }
        /* ── BeginFunc name n ── */
        else if (strncmp(p, "BeginFunc", 9) == 0) {
            char name[100]; int n;
            sscanf(p, "BeginFunc %s %d", name, &n);
            strcpy(op, "BeginFunc");
            strcpy(arg1, name);
            sprintf(arg2, "%d params", n);
        }
        /* ── EndFunc name ── */
        else if (strncmp(p, "EndFunc", 7) == 0) {
            char name[100]; sscanf(p, "EndFunc %s", name);
            strcpy(op, "EndFunc");
            strcpy(arg1, name);
        }
        /* ── PopParam var ── */
        else if (strncmp(p, "PopParam", 8) == 0) {
            sscanf(p, "PopParam %s", arg1);
            strcpy(op, "PopParam");
        }
        /* ── PushParam var ── */
        else if (strncmp(p, "PushParam", 9) == 0) {
            sscanf(p, "PushParam %s", arg1);
            strcpy(op, "PushParam");
        }
        /* ── Return val / Return ── */
        else if (strncmp(p, "Return", 6) == 0) {
            strcpy(op, "Return");
            char val[200]="";
            sscanf(p, "Return %s", val);
            if (val[0]) strcpy(arg1, val);
        }
        /* ── goto L ── */
        else if (strncmp(p, "goto", 4) == 0 &&
                 (p[4]==' '||p[4]=='\0') &&
                 (strstr(p,"if ")==NULL || strstr(p,"if ")>p+4)) {
            char lbl[50]; sscanf(p, "goto %s", lbl);
            strcpy(op, "goto");
            strcpy(arg1, lbl);
        }
        /* ── if a1 rel a2 goto L ── */
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
        /* ── print* / input* ── */
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
        /* ── Call (statement form): Call fname ── */
        else if (strncmp(p, "Call ", 5) == 0) {
            char fname[100]; sscanf(p, "Call %s", fname);
            strcpy(op, "Call");
            strcpy(arg1, fname);
        }
        /* ── assignment forms: something = something ── */
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
                /* no '=' — treat as raw opcode line */
                strcpy(op, p);
            }
        }
        { int l; 
          l=strlen(op);    while(l>0&&(op[l-1]==' '   ||op[l-1]=='\n'))   op[--l]='\0';
          l=strlen(arg1);  while(l>0&&(arg1[l-1]==' ' ||arg1[l-1]=='\n')) arg1[--l]='\0';
          l=strlen(arg2);  while(l>0&&(arg2[l-1]==' ' ||arg2[l-1]=='\n')) arg2[--l]='\0';
          l=strlen(result);while(l>0&&(result[l-1]==' '||result[l-1]=='\n'))result[--l]='\0';
        }
        printf("  %-4d  %-18s  %-18s  %-18s  %-18s\n",
               q++, op, arg1, arg2, result);
    }
    printf("================================================================================\n");
    printf("  Total quadruples: %d\n", q);
    printf("================================================================================\n");
}
void generateSymbolTableDOT() {
    FILE* dot = fopen("symbol_table.dot", "w");
    fprintf(dot, "digraph SymbolTable {\n");
    fprintf(dot, "  rankdir=TB;\n");
    fprintf(dot, "  node [shape=record, style=filled, fontname=\"Helvetica\"];\n\n");
    for (int i = 0; i < env_count; i++) {
        Table* table = envs[i]->table;
        int has_syms = 0;
        for (int j = 0; j < table->size; j++)
            if (table->buckets[j]) { has_syms = 1; break; }
        const char* scope_label = (i == 0) ? "Global" : "Local";
        const char* color = (i == 0) ? "\"#fffacd\"" : "\"#d0e8ff\"";
        fprintf(dot, "  scope%d [fillcolor=%s, label=\"{<h> Scope %d : %s",
                i, color, i, scope_label);
        if (!has_syms) {
            fprintf(dot, " | (empty)");
        } else {
            for (int j = 0; j < table->size; j++) {
                TableEntry* entry = table->buckets[j];
                while (entry) {
                    Symbol* s = entry->value;
                    char type_str[200];
                    strcpy(type_str, s->type);
                    char base[100];
                    strncpy(base, s->type, sizeof(base)-1);
                    base[sizeof(base)-1] = '\0';
                    char* bracket = strchr(base, '[');
                    if (bracket) *bracket = '\0';
                    if (s->dim_count > 0) {
                        strcpy(type_str, base);
                        for (int d = 0; d < s->dim_count; d++) {
                            char part[20];
                            sprintf(part, "[%d]", s->dimensions[d]);
                            strcat(type_str, part);
                        }
                    } else {
                        strcpy(type_str, base);
                    }
                    fprintf(dot, " | %s : %s  [line %d]",
                        s->name, type_str, s->decl_line);
                    entry = entry->next;
                }
            }
        }
        fprintf(dot, "}\"];\n");
    }
    fprintf(dot, "\n");
    for (int i = 0; i < env_count; i++) {
        if (envs[i]->prev != NULL) {
            for (int k = 0; k < i; k++) {
                if (envs[k] == envs[i]->prev) {
                    fprintf(dot, "  scope%d -> scope%d;\n", k, i);  /* parent -> child */
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
    fprintf(dot, "  node [shape=box, style=filled, fillcolor=lightblue];\n");
    fprintf(dot, "  compound=true;\n");
 
    // Split into per-function subgraphs
    char cur_func[100] = "";
    int in_func = 0;
    int global_open = 0;
 
    for (int i = 0; i < code; i++) {
        char label[10000];
        strcpy(label, imcode[i]);
        char* newline = strchr(label, '\n');
        if (newline) *newline = '\0';
 
        // Escape quotes
        char safe[10000]; int si = 0;
        for (int ci = 0; label[ci]; ci++) {
            if (label[ci] == '"') { safe[si++] = '\\'; safe[si++] = '"'; }
            else safe[si++] = label[ci];
        }
        safe[si] = '\0';
 
        // If we are outside any function and this is not a BeginFunc,
        // it is a global-scope statement (like Python top-level code).
        // Open a "Global Scope" cluster the first time we encounter one.
        if (!in_func && strstr(imcode[i], "BeginFunc") == NULL) {
            // Open global scope subgraph on the very first global line
            if (!global_open) {
                fprintf(dot, "\n  subgraph cluster_global {\n");
                fprintf(dot, "    label=\"Global Scope\";\n");
                fprintf(dot, "    style=rounded; color=gray40; bgcolor=\"#f5f5dc\";\n");
                global_open = 1;
            }
            fprintf(dot, "    n%d [label=\"%s\"];\n", i, safe);
 
            // Detect instruction type for global scope
            int is_call_g = (strstr(imcode[i], "Call ") != NULL);
 
            // Detect conditional: must have " if " (with spaces) before "goto"
            int is_cond_g = 0;
            {
                char* if_ptr   = strstr(imcode[i], " if ");
                char* goto_ptr = strstr(imcode[i], "goto");
                if (if_ptr && goto_ptr && if_ptr < goto_ptr) is_cond_g = 1;
            }
 
            // Detect unconditional goto (not a call)
            int is_goto_g = (!is_cond_g && !is_call_g && strstr(imcode[i], "goto") != NULL);
 
            if (is_cond_g) {
                // Conditional: green edge to jump target, red edge to fall-through
                char* goto_ptr = strstr(imcode[i], "goto");
                char* ptr = goto_ptr + 4;
                while (*ptr == ' ' || *ptr == '\t') ptr++;
                if (isdigit(*ptr)) {
                    int target = atoi(ptr);
                    fprintf(dot, "    n%d -> n%d [label=\"true\", color=green, penwidth=2];\n", i, target);
                }
                if (i + 1 < code && strstr(imcode[i+1], "BeginFunc") == NULL)
                    fprintf(dot, "    n%d -> n%d [label=\"false\", color=red, penwidth=2];\n", i, i+1);
            } else if (is_goto_g) {
                // Unconditional goto
                char* goto_ptr = strstr(imcode[i], "goto");
                char* ptr = goto_ptr + 4;
                while (*ptr == ' ' || *ptr == '\t') ptr++;
                if (isdigit(*ptr)) {
                    int target = atoi(ptr);
                    fprintf(dot, "    n%d -> n%d [label=\"goto\"];\n", i, target);
                }
            } else if (is_call_g) {
                char callee[100] = "";
                char* call_ptr = strstr(imcode[i], "Call ");
                if (call_ptr) sscanf(call_ptr, "Call %s", callee);
                for (int ci = 0; callee[ci]; ci++) {
                    if (callee[ci] == '\n' || callee[ci] == ' ') { callee[ci] = '\0'; break; }
                }
                int callee_begin = -1, callee_end = -1;
                for (int j = 0; j < code; j++) {
                    if (strstr(imcode[j], "BeginFunc") != NULL) {
                        char fname[100]; sscanf(imcode[j], "%*d BeginFunc %s", fname);
                        if (strcmp(fname, callee) == 0) callee_begin = j;
                    }
                    if (strstr(imcode[j], "EndFunc") != NULL) {
                        char fname[100]; sscanf(imcode[j], "%*d EndFunc %s", fname);
                        if (strcmp(fname, callee) == 0) callee_end = j;
                    }
                }
                if (callee_begin >= 0)
                    fprintf(dot, "    n%d -> n%d [label=\"call\", color=darkorange, style=bold, constraint=false];\n", i, callee_begin);
                if (callee_end >= 0 && i + 1 < code)
                    fprintf(dot, "    n%d -> n%d [label=\"ret\", color=purple, style=dashed, constraint=false];\n", callee_end, i+1);
                // sequential to next global line
                if (i + 1 < code && strstr(imcode[i+1], "BeginFunc") == NULL)
                    fprintf(dot, "    n%d -> n%d [style=dashed];\n", i, i+1);
            } else {
                // Sequential fall-through
                int next_is_begin = (i + 1 < code && strstr(imcode[i+1], "BeginFunc") != NULL);
                if (i + 1 < code && !next_is_begin)
                    fprintf(dot, "    n%d -> n%d [style=dashed];\n", i, i+1);
            }
            
            // Check if we should close the global cluster
            // Close when: next instruction is BeginFunc OR we've reached the end
            int should_close = 0;
            if (i + 1 >= code) {
                should_close = 1; // End of code
            } else if (strstr(imcode[i+1], "BeginFunc") != NULL) {
                should_close = 1; // Next is a function
            }
            
            if (should_close && global_open) {
                fprintf(dot, "  }\n"); // close global cluster
                global_open = 0;
            }
            
            continue;
        }
 
        if (strstr(imcode[i], "BeginFunc") != NULL) {
            sscanf(imcode[i], "%*d BeginFunc %s", cur_func);
            fprintf(dot, "\n  subgraph cluster_%s {\n", cur_func);
            fprintf(dot, "    label=\"Function: %s\";\n", cur_func);
            fprintf(dot, "    style=rounded; color=steelblue; bgcolor=\"#e8f4f8\";\n");
            in_func = 1;
            fprintf(dot, "    n%d [label=\"%s\", shape=oval, fillcolor=\"#aaddff\"];\n", i, safe);
            // BeginFunc -> first body instruction
            if (i + 1 < code) {
                fprintf(dot, "    n%d -> n%d [style=dashed];\n", i, i+1);
            }
            continue;
        }
 
        if (strstr(imcode[i], "EndFunc") != NULL) {
            fprintf(dot, "    n%d [label=\"%s\", shape=oval, fillcolor=\"#aaddff\"];\n", i, safe);
            // Edge into EndFunc drawn by Return handler or sequential else-branch.
            fprintf(dot, "  }\n"); // close subgraph
            in_func = 0;
            cur_func[0] = '\0';
            continue;
        }
 
        fprintf(dot, "    n%d [label=\"%s\"];\n", i, safe);
 
        int is_conditional = 0;
        if (strstr(imcode[i], "if") != NULL && strstr(imcode[i], "goto") != NULL) {
            char* if_ptr = strstr(imcode[i], "if");
            char* goto_ptr = strstr(imcode[i], "goto");
            if (if_ptr < goto_ptr) is_conditional = 1;
        }
 
        // Detect "Call funcname" or "t = Call funcname"
        int is_call = (strstr(imcode[i], "Call ") != NULL);
 
        if (is_conditional) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                fprintf(dot, "    n%d -> n%d [label=\"true\", color=green, penwidth=2];\n", i, target);
            }
            if (i + 1 < code) {
                fprintf(dot, "    n%d -> n%d [label=\"false\", color=red, penwidth=2];\n", i, i+1);
            }
        }
        else if (strstr(imcode[i], "goto") != NULL && !is_call) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) {
                int target = atoi(ptr);
                fprintf(dot, "    n%d -> n%d [label=\"goto\"];\n", i, target);
            }
        }
        else if (strstr(imcode[i], "Return") != NULL) {
            // Return -> EndFunc (always next line)
            if (i + 1 < code && strstr(imcode[i+1], "EndFunc") != NULL) {
                fprintf(dot, "    n%d -> n%d [style=dashed];\n", i, i+1);
            }
        }
        else if (is_call) {
            // Extract callee name from "N Call foo" or "N t = Call foo"
            char callee[100] = "";
            char* call_ptr = strstr(imcode[i], "Call ");
            if (call_ptr) sscanf(call_ptr, "Call %s", callee);
            // Remove trailing newline/space from callee
            for (int ci = 0; callee[ci]; ci++) {
                if (callee[ci] == '\n' || callee[ci] == ' ') { callee[ci] = '\0'; break; }
            }
 
            // Find BeginFunc of callee
            int callee_begin = -1, callee_end = -1;
            for (int j = 0; j < code; j++) {
                if (strstr(imcode[j], "BeginFunc") != NULL) {
                    char fname[100];
                    sscanf(imcode[j], "%*d BeginFunc %s", fname);
                    if (strcmp(fname, callee) == 0) { callee_begin = j; }
                }
                if (strstr(imcode[j], "EndFunc") != NULL) {
                    char fname[100];
                    sscanf(imcode[j], "%*d EndFunc %s", fname);
                    if (strcmp(fname, callee) == 0) { callee_end = j; }
                }
            }
 
            // Call edge: call site -> callee BeginFunc  (orange, labeled "call")
            if (callee_begin >= 0) {
                fprintf(dot, "    n%d -> n%d [label=\"call\", color=darkorange, style=bold, constraint=false];\n", i, callee_begin);
            }
            // Return edge: callee EndFunc -> instruction after call site  (purple, labeled "return")
            if (callee_end >= 0 && i + 1 < code) {
                fprintf(dot, "    n%d -> n%d [label=\"ret\", color=purple, style=dashed, constraint=false];\n", callee_end, i+1);
            }
 
            // Sequential flow: call site -> next instruction (normal dashed)
            if (i + 1 < code && strstr(imcode[i+1], "BeginFunc") == NULL
                              && strstr(imcode[i+1], "EndFunc")   == NULL) {
                fprintf(dot, "    n%d -> n%d [style=dashed];\n", i, i+1);
            }
        }
        else {
            // Sequential — never cross into another function's BeginFunc
            if (i + 1 < code && strstr(imcode[i+1], "BeginFunc") == NULL) {
                fprintf(dot, "    n%d -> n%d [style=dashed];\n", i, i+1);
            }
        }
    }
 
    // Make sure to close global cluster if it's still open
    if (global_open) {
        fprintf(dot, "  }\n");
    }
 
    fprintf(dot, "}\n");
    fclose(dot);
}




void identifyBasicBlocks() {
    int is_leader[10000] = {0};
    is_leader[0] = 1;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;
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
            if (i + 1 < code) {
                is_leader[i + 1] = 1;
            }
        }
        if (strstr(imcode[i], "BeginFunc") != NULL) {
            is_leader[i] = 1;
            if (i + 1 < code) is_leader[i + 1] = 1;
        }
        if (strstr(imcode[i], "EndFunc") != NULL) {
            is_leader[i] = 1;
            if (i + 1 < code) is_leader[i + 1] = 1;
        }
        if (strstr(imcode[i], "Return") != NULL) {
            if (i + 1 < code) is_leader[i + 1] = 1;
        }
    }
    int current_start = -1;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "// DEAD") != NULL) continue;       
        if (is_leader[i]) {
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
    if (current_start != -1) {
        BasicBlock* bb = (BasicBlock*)malloc(sizeof(BasicBlock));
        bb->start_line = current_start;
        bb->end_line = code - 1;
        bb->block_id = block_count++;
        bb->next = blocks;
        blocks = bb;
    }
    
}
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
void generateTACFlowWithBlocks() {
    identifyBasicBlocks();
    FILE* dot = fopen("tac_flow_blocks.dot", "w");
    fprintf(dot, "digraph TAC_Blocks {\n");
    fprintf(dot, "  node [shape=record, style=filled, fillcolor=lightblue];\n");
    fprintf(dot, "  rankdir=TB;\n\n");
    BasicBlock* bb = blocks;
    while (bb) {
        int is_global = 1;
        for (int i = bb->start_line; i <= bb->end_line && i < code; i++) {
            if (strstr(imcode[i], "BeginFunc") != NULL || strstr(imcode[i], "EndFunc") != NULL) {
                is_global = 0; break;
            }
        }
        {
            int inside = 0;
            for (int i = 0; i < code; i++) {
                if (strstr(imcode[i], "BeginFunc") != NULL) inside = 1;
                if (i >= bb->start_line && i <= bb->end_line && inside) { is_global = 0; break; }
                if (strstr(imcode[i], "EndFunc") != NULL) inside = 0;
            }
        }
        if (is_global)
            fprintf(dot, "  bb%d [label=\"{<b>Global Scope|", bb->block_id);
        else
            fprintf(dot, "  bb%d [label=\"{<b>Block %d|", bb->block_id, bb->block_id);
        int first = 1;
        for (int i = bb->start_line; i <= bb->end_line && i < code; i++) { 
            char label[10000];
            strcpy(label, imcode[i]);
            char escaped[10000];
            int j = 0, k = 0;
            while (label[j] != '\0' && label[j] != '\n') {
                if (label[j] == '\\' ||   
        label[j] == '"'  ||   label[j] == '|' || label[j] == '{' || label[j] == '}' || 
                    label[j] == '<' || label[j] == '>') {
                    escaped[k++] = '\\';
                }
                escaped[k++] = label[j++];
            }
            escaped[k] = '\0';
            
            if (!first) fprintf(dot, "\\l");  // Left-aligned line break
            fprintf(dot, "%s", escaped);
            first = 0;
        }
        fprintf(dot, "\\l}\"];\n");
        bb = bb->next;
    }
    fprintf(dot, "\n  // Control flow edges\n");
    typedef struct EdgeSeen { int a, b; } EdgeSeen;
    EdgeSeen call_edges_seen[1000]; int call_edge_count = 0;
    EdgeSeen ret_edges_seen[1000];  int ret_edge_count  = 0;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "Call ") == NULL) continue;
        char callee[100] = "";
        char* call_ptr = strstr(imcode[i], "Call ");
        if (call_ptr) sscanf(call_ptr, "Call %s", callee);
        for (int ci = 0; callee[ci]; ci++)
            if (callee[ci] == '\n' || callee[ci] == ' ') { callee[ci] = '\0'; break; }
        int callee_begin = -1, callee_end = -1;
        for (int j = 0; j < code; j++) {
            if (strstr(imcode[j], "BeginFunc") != NULL) {
                char fname[100]; sscanf(imcode[j], "%*d BeginFunc %s", fname);
                if (strcmp(fname, callee) == 0) callee_begin = j;
            }
            if (strstr(imcode[j], "EndFunc") != NULL) {
                char fname[100]; sscanf(imcode[j], "%*d EndFunc %s", fname);
                if (strcmp(fname, callee) == 0) callee_end = j;
            }
        }
        int src_block = getBlockForLine(i);
        if (src_block == -1) continue;
        if (callee_begin >= 0) {
            int dst = getBlockForLine(callee_begin);
            if (dst != -1) {
                int seen = 0;
                for (int x = 0; x < call_edge_count; x++)
                    if (call_edges_seen[x].a == src_block && call_edges_seen[x].b == dst) { seen = 1; break; }
                if (!seen) {
                    fprintf(dot, "  bb%d -> bb%d [label=\"call\", color=darkorange, style=bold, constraint=false];\n",
                            src_block, dst);
                    call_edges_seen[call_edge_count++] = (EdgeSeen){src_block, dst};
                }
            }
        }
        if (callee_end >= 0 && i + 1 < code) {
            int ret_src = getBlockForLine(callee_end);
            int ret_dst = getBlockForLine(i + 1);
            if (ret_src != -1 && ret_dst != -1) {
                int seen = 0;
                for (int x = 0; x < ret_edge_count; x++)
                    if (ret_edges_seen[x].a == ret_src && ret_edges_seen[x].b == ret_dst) { seen = 1; break; }
                if (!seen) {
                    fprintf(dot, "  bb%d -> bb%d [label=\"ret\", color=purple, style=dashed, constraint=false];\n",
                            ret_src, ret_dst);
                    ret_edges_seen[ret_edge_count++] = (EdgeSeen){ret_src, ret_dst};
                }
            }
        }
    }
    for (int i = 0; i < code; i++) {
        int current_block = getBlockForLine(i);
        if (current_block == -1) continue;
        bb = blocks;
        int is_block_end = 0;
        while (bb) {
            if (bb->block_id == current_block && i == bb->end_line) { is_block_end = 1; break; }
            bb = bb->next;
        }
        if (!is_block_end) continue;
        int is_conditional = 0;
        if (strstr(imcode[i], "if") != NULL && strstr(imcode[i], "goto") != NULL) {
            char* if_ptr = strstr(imcode[i], "if");
            char* goto_ptr = strstr(imcode[i], "goto");
            if (if_ptr < goto_ptr) is_conditional = 1;
        }
        int is_call = (strstr(imcode[i], "Call ") != NULL);
        if (is_conditional) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) {
                int target_block = getBlockForLine(atoi(ptr));
                if (target_block != -1)
                    fprintf(dot, "  bb%d -> bb%d [label=\"T\", color=green, penwidth=2];\n",
                            current_block, target_block);
            }
            if (i + 1 < code) {
                int next_block = getBlockForLine(i + 1);
                if (next_block != -1 && next_block != current_block)
                    fprintf(dot, "  bb%d -> bb%d [label=\"F\", color=red, penwidth=2];\n",
                            current_block, next_block);
            }
        }
        else if (strstr(imcode[i], "goto") != NULL && !is_call) {
            char* goto_ptr = strstr(imcode[i], "goto");
            char* ptr = goto_ptr + 4;
            while (*ptr == ' ' || *ptr == '\t') ptr++;
            if (isdigit(*ptr)) {
                int target_block = getBlockForLine(atoi(ptr));
                if (target_block != -1)
                    fprintf(dot, "  bb%d -> bb%d [label=\"goto\", penwidth=2];\n",
                            current_block, target_block);
            }
        }
        else if (strstr(imcode[i], "Return") != NULL) {
            if (i + 1 < code) {
                int next_block = getBlockForLine(i + 1);
                if (next_block != -1 && next_block != current_block)
                    fprintf(dot, "  bb%d -> bb%d [style=dashed, color=black];\n",
                            current_block, next_block);
            }
        }
        else if (is_call) {
            if (i + 1 < code && strstr(imcode[i+1], "BeginFunc") == NULL
                              && strstr(imcode[i+1], "EndFunc")   == NULL) {
                int next_block = getBlockForLine(i + 1);
                if (next_block != -1 && next_block != current_block)
                    fprintf(dot, "  bb%d -> bb%d [style=dashed, color=black];\n",
                            current_block, next_block);
            }
        }
        else if (strstr(imcode[i], "EndFunc") == NULL) {
            if (i + 1 < code && strstr(imcode[i+1], "BeginFunc") == NULL) {
                int next_block = getBlockForLine(i + 1);
                if (next_block != -1 && next_block != current_block)
                    fprintf(dot, "  bb%d -> bb%d [style=dashed, color=black];\n",
                            current_block, next_block);
            }
        }
    }   
    fprintf(dot, "}\n");
    fclose(dot);
}
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
void generateCallGraphDOT() {
    FILE* dot = fopen("call_graph.dot", "w");
    fprintf(dot, "digraph CallGraph {\n");
    fprintf(dot, "  node [shape=record, style=filled, fillcolor=lightblue];\n");
    fprintf(dot, "  rankdir=TB;\n");
    fprintf(dot, "  concentrate=true;\n\n");
    typedef struct CallEdge {
        char caller[100];
        char callee[100];
        int line_number;
        int call_count;
        struct CallEdge* next;
    } CallEdge;
    CallEdge* edges = NULL;
    char current_func[100] = "";
    typedef struct FuncMetrics {
        char name[100];
        int tac_lines;
        int start_line;
        int end_line;
        int call_count;  
        struct FuncMetrics* next;
    } FuncMetrics;   
    FuncMetrics* metrics = NULL;
    for (int i = 0; i < code; i++) {
        if (strstr(imcode[i], "BeginFunc") != NULL) {
            int param_count;
            sscanf(imcode[i], "%*d BeginFunc %s %d", current_func, &param_count);
            FuncMetrics* m = malloc(sizeof(FuncMetrics));
            strcpy(m->name, current_func);
            m->start_line = i;
            m->tac_lines = 0;
            m->call_count = 0;
            m->next = metrics;
            metrics = m;
        }     
        if (strstr(imcode[i], "EndFunc") != NULL && strcmp(current_func, "") != 0) {
            FuncMetrics* m = metrics;
            while (m) {
                if (strcmp(m->name, current_func) == 0) {
                    m->end_line = i;
                   for (int j = m->start_line; j <= m->end_line; j++) {
                        if (strstr(imcode[j], "// DEAD") == NULL &&
                            strstr(imcode[j], "BeginFunc") == NULL &&
                            strstr(imcode[j], "EndFunc") == NULL &&
                            strstr(imcode[j], "PopParam") == NULL &&
                            strstr(imcode[j], "PushParam") == NULL) {
                            m->tac_lines++;
                        }
                    }
                    break;
                }
                m = m->next;
            }
        }
        if (strstr(imcode[i], "Call") != NULL && strcmp(current_func, "") != 0) {
            char callee[100];
            if (sscanf(imcode[i], "%*d %*s = Call %s", callee) == 1 ||
                sscanf(imcode[i], "%*d Call %s", callee) == 1) {
                FuncMetrics* m = metrics;
                while (m) {
                    if (strcmp(m->name, callee) == 0) {
                        m->call_count++;
                        break;
                    }
                    m = m->next;
                }
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
    Function* f = func_list;
    while (f) {
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
        const char* complexity;
        if (tac_lines < 5) complexity = "Simple";
        else if (tac_lines < 20) complexity = "Medium";
        else complexity = "Complex";
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
    CallEdge* e = edges;
    while (e) {
        const char* color = "black";
        int penwidth = 1;
        if (e->call_count > 5) {
            penwidth = 3;
            color = "red";
        } else if (e->call_count > 2) {
            penwidth = 2;
            color = "orange";
        }
        fprintf(dot, "  \"%s\" -> \"%s\" [label=\"%d call%s\", "
             "color=\"%s\", penwidth=%d];\n",
        e->caller, e->callee, 
        e->call_count, e->call_count == 1 ? "" : "s",
        color, penwidth);
        e = e->next;
    }
    fprintf(dot, "\n  // Legend\n");
    fprintf(dot, "  legend [shape=none, margin=0, label=<\n");
    fprintf(dot, "    <TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\">\n");
    fprintf(dot, "      <TR><TD>Black edge</TD><TD>Called 1-2 times</TD></TR>\n");
    fprintf(dot, "      <TR><TD><FONT COLOR=\"orange\">Orange edge</FONT></TD><TD>Called 3-5 times</TD></TR>\n");
    fprintf(dot, "      <TR><TD><FONT COLOR=\"red\">Red edge</FONT></TD><TD>Called 6+ times</TD></TR>\n");
    fprintf(dot, "    </TABLE>\n");
    fprintf(dot, "  >];\n");
    fprintf(dot, "}\n");
    fclose(dot);
    FuncMetrics* m = metrics;
    while (m) {
        if (m->call_count > 0) {
        }
        m = m->next;
    }
    m = metrics;
    while (m) {
        const char* complexity;
        if (m->tac_lines < 5) complexity = "Simple";
        else if (m->tac_lines < 15) complexity = "Medium";
        else complexity = "Complex";
        m = m->next;
    }
}
void generateAsmPage() {
    FILE* html = fopen("asm.html", "w");
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Assembly - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "<style>\n");
    fprintf(html, ".asm-directive { color: #79c0ff; }\n");
    fprintf(html, ".asm-label     { color: #ffa657; font-weight: 700; }\n");
    fprintf(html, ".asm-comment   { color: #8b949e; font-style: italic; }\n");
    fprintf(html, ".asm-instr     { color: #e6edf3; }\n");
    fprintf(html, ".line-num      { color: #4b5563; user-select: none; min-width: 40px;\n");
    fprintf(html, "                 display: inline-block; margin-right: 12px; text-align: right; }\n");
    fprintf(html, ".toggle-container { display: flex; align-items: center; gap: 15px;\n");
    fprintf(html, "    padding: 12px 20px; background: #111827; border-radius: 8px;\n");
    fprintf(html, "    border: 1px solid rgba(41,227,60,0.2); margin-left: auto; }\n");
    fprintf(html, ".toggle-label  { font-size: 14px; color: #9ca3af; font-weight: 600; }\n");
    fprintf(html, ".asm-stats     { display: flex; gap: 20px; margin-bottom: 16px; flex-wrap: wrap; }\n");
    fprintf(html, ".asm-stat      { background: #111827; border: 1px solid rgba(41,227,60,0.2);\n");
    fprintf(html, "                 border-radius: 8px; padding: 10px 20px; text-align: center; }\n");
    fprintf(html, ".asm-stat .num { font-size: 1.6em; font-weight: 700;\n");
    fprintf(html, "    background: linear-gradient(90deg,rgba(97,215,101,1) 0%%,rgba(225,255,64,1) 100%%);\n");
    fprintf(html, "    -webkit-background-clip: text; -webkit-text-fill-color: transparent;\n");
    fprintf(html, "    background-clip: text; }\n");
    fprintf(html, ".asm-stat .lbl { color: #9ca3af; font-size: 0.8em; margin-top: 2px; }\n");
    fprintf(html, ".search-bar    { display: flex; gap: 10px; margin-bottom: 16px; }\n");
    fprintf(html, ".search-bar input { flex: 1; background: #111827;\n");
    fprintf(html, "    border: 1px solid rgba(41,227,60,0.2); color: #f3f4f6;\n");
    fprintf(html, "    border-radius: 8px; padding: 10px 16px; font-size: 14px; outline: none; }\n");
    fprintf(html, ".search-bar input:focus { border-color: rgba(41,227,60,0.6); }\n");
    fprintf(html, ".search-bar input::placeholder { color: #4b5563; }\n");
    fprintf(html, ".highlight     { background: rgba(255,214,0,0.25); border-radius: 3px; }\n");
    fprintf(html, "</style>\n");
    fprintf(html, "</head>\n<body>\n");
    fprintf(html, "<div class=\"page-header\">\n");
    fprintf(html, "<div class=\"header2\">\n");
    fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
    fprintf(html, "<h1>Assembly Code</h1>\n");
    fprintf(html, "<div class=\"toggle-container\">\n");
    fprintf(html, "<span class=\"toggle-label\" id=\"lineCountLabel\">Loading...</span>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"asm-stats\" id=\"asmStats\"></div>\n");
    fprintf(html, "<div class=\"search-bar\">\n");
    fprintf(html, "<input type=\"text\" id=\"searchInput\" placeholder=\"Search instruction, register, label...\" oninput=\"doSearch()\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"code-viewer\" id=\"codeViewer\"><div class=\"loading\">Loading assembly...</div></div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<script>\n");
    fprintf(html, "let asmLines = [];\n");
    fprintf(html, "let searchTerm = '';\n");
    fprintf(html, "async function loadAsm() {\n");
    fprintf(html, "    try {\n");
    fprintf(html, "        const r = await fetch('output.s');\n");
    fprintf(html, "        if (!r.ok) throw new Error('Not found');\n");
    fprintf(html, "        const txt = await r.text();\n");
    fprintf(html, "        asmLines = txt.split('\\n');\n");
    fprintf(html, "        document.getElementById('lineCountLabel').textContent = asmLines.length + ' lines';\n");
    //fprintf(html, "        computeStats();\n");
    fprintf(html, "        renderLines(asmLines);\n");
    fprintf(html, "    } catch(e) {\n");
    fprintf(html, "        document.getElementById('codeViewer').innerHTML =\n");
    fprintf(html, "            '<div style=\"color:#ff6b6b;padding:20px;text-align:center;\">Could not load output.s</div>';\n");
    fprintf(html, "    }\n");
    fprintf(html, "}\n");
    fprintf(html, "function computeStats() {\n");
    fprintf(html, "    let instrs=0, labels=0, directives=0, comments=0;\n");
    fprintf(html, "    asmLines.forEach(l => {\n");
    fprintf(html, "        const t = l.trim();\n");
    fprintf(html, "        if (!t) return;\n");
    fprintf(html, "        if (t.startsWith('#')) comments++;\n");
    fprintf(html, "        else if (t.startsWith('.')) directives++;\n");
    fprintf(html, "        else if (t.endsWith(':')) labels++;\n");
    fprintf(html, "        else instrs++;\n");
    fprintf(html, "    });\n");
    fprintf(html, "    document.getElementById('asmStats').innerHTML = [\n");
    fprintf(html, "        ['Instructions',instrs],['Labels',labels],\n");
    fprintf(html, "        ['Directives',directives],['Comments',comments]\n");
    fprintf(html, "    ].map(([l,n]) => `<div class='asm-stat'><div class='num'>${n}</div><div class='lbl'>${l}</div></div>`).join('');\n");
    fprintf(html, "}\n");
    fprintf(html, "function classify(line) {\n");
    fprintf(html, "    const t = line.trim();\n");
    fprintf(html, "    if (!t) return 'asm-instr';\n");
    fprintf(html, "    if (t.startsWith('#')) return 'asm-comment';\n");
    fprintf(html, "    if (t.startsWith('.')) return 'asm-directive';\n");
    fprintf(html, "    if (t.endsWith(':')) return 'asm-label';\n");
    fprintf(html, "    return 'asm-instr';\n");
    fprintf(html, "}\n");
    fprintf(html, "function escHtml(s) {\n");
    fprintf(html, "    return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');\n");
    fprintf(html, "}\n");
    fprintf(html, "function renderLines(lines) {\n");
    fprintf(html, "    document.getElementById('codeViewer').innerHTML = lines.map((line,i) => {\n");
    fprintf(html, "        const cls = classify(line);\n");
    fprintf(html, "        let content = escHtml(line);\n");
    fprintf(html, "        if (searchTerm && content.toLowerCase().includes(searchTerm)) {\n");
    fprintf(html, "            const re = new RegExp(searchTerm.replace(/[.*+?^${}()|[\\\\]\\\\\\\\]/g,'\\\\\\\\$&'),'gi');\n");
    fprintf(html, "            content = content.replace(re, m => `<mark class='highlight'>${m}</mark>`);\n");
    fprintf(html, "        }\n");
    fprintf(html, "        return `<span class='code-line ${cls}'><span class='line-num'>${i+1}</span>${content}</span>`;\n");
    fprintf(html, "    }).join('');\n");
    fprintf(html, "}\n");
    fprintf(html, "function doSearch() {\n");
    fprintf(html, "    searchTerm = document.getElementById('searchInput').value.trim().toLowerCase();\n");
    fprintf(html, "    renderLines(asmLines);\n");
    fprintf(html, "    if (searchTerm) {\n");
    fprintf(html, "        const first = document.querySelector('.highlight');\n");
    fprintf(html, "        if (first) first.scrollIntoView({block:'center'});\n");
    fprintf(html, "    }\n");
    fprintf(html, "}\n");
    fprintf(html, "loadAsm();\n");
    fprintf(html, "</script>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateTACPage() {
    FILE* html = fopen("tac.html", "w");
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>TAC Code - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "<style>\n");
    fprintf(html, ".toggle-container {\n");
fprintf(html, "    display: flex;\n");
fprintf(html, "    align-items: center;\n");
fprintf(html, "    gap: 15px;\n");
fprintf(html, "    padding: 12px 20px;\n");
fprintf(html, "    background: #111827;\n");
fprintf(html, "    border-radius: 8px;\n");
fprintf(html, "    border: 1px solid rgba(41, 227, 60, 0.2);\n");
fprintf(html, "    margin-left: auto;\n");
fprintf(html, "    margin-bottom: 25px;\n");
fprintf(html, "       margin-top: 18px;\n");
fprintf(html, "}\n");
    fprintf(html, ".toggle-label {\n");
    fprintf(html, "    font-size: 17px;\n");
    fprintf(html, "    color: #c7cacf;\n");
    fprintf(html, "    font-weight: 700;\n");
    fprintf(html, "}\n");
    fprintf(html, ".toggle-switch {\n");
    fprintf(html, "    position: relative;\n");
    fprintf(html, "    display: inline-block;\n");
    fprintf(html, "    width: 60px;\n");
    fprintf(html, "    height: 30px;\n");
    fprintf(html, "}\n");
    fprintf(html, ".toggle-switch input {\n");
    fprintf(html, "    opacity: 0;\n");
    fprintf(html, "    width: 0;\n");
    fprintf(html, "    height: 0;\n");
    fprintf(html, "}\n");
    fprintf(html, ".slider {\n");
    fprintf(html, "    position: absolute;\n");
    fprintf(html, "    cursor: pointer;\n");
    fprintf(html, "    top: 0;\n");
    fprintf(html, "    left: 0;\n");
    fprintf(html, "    right: 0;\n");
    fprintf(html, "    bottom: 0;\n");
    fprintf(html, "    background-color: #3b82f6;\n");
    fprintf(html, "    transition: .4s;\n");
    fprintf(html, "    border-radius: 30px;\n");
    fprintf(html, "    box-shadow: 0 2px 4px rgba(0, 0, 0, 0.3);\n");
    fprintf(html, "}\n");
    fprintf(html, ".slider:before {\n");
    fprintf(html, "    position: absolute;\n");
    fprintf(html, "    content: '';\n");
    fprintf(html, "    height: 22px;\n");
    fprintf(html, "    width: 22px;\n");
    fprintf(html, "    left: 4px;\n");
    fprintf(html, "    bottom: 4px;\n");
    fprintf(html, "    background-color: white;\n");
    fprintf(html, "    transition: .4s;\n");
    fprintf(html, "    border-radius: 50%%;\n");
    fprintf(html, "}\n");
    fprintf(html, "input:checked + .slider {\n");
    fprintf(html, "    background: linear-gradient(90deg, rgba(97,215,101,1) 0%%, rgba(41,227,60,1) 100%%);\n");
    fprintf(html, "}\n");
    fprintf(html, "input:checked + .slider:before {\n");
    fprintf(html, "    transform: translateX(30px);\n");
    fprintf(html, "}\n");
    fprintf(html, ".toggle-status {\n");
    fprintf(html, "    font-size: 17px;\n");
    fprintf(html, "    font-weight: 700;\n");
    fprintf(html, "    min-width: 110px;\n");
    fprintf(html, "    background: linear-gradient(90deg, rgba(97,215,101,1) 0%%, rgba(225,255,64,1) 100%%);\n");
    fprintf(html, "    -webkit-background-clip: text;\n");
    fprintf(html, "    -webkit-text-fill-color: transparent;\n");
    fprintf(html, "    background-clip: text;\n");
    fprintf(html, "}\n");
    fprintf(html, ".toggle-status.unoptimized {\n");
    fprintf(html, "    background: #3b82f6;\n");
    fprintf(html, "    -webkit-background-clip: text;\n");
    fprintf(html, "    -webkit-text-fill-color: transparent;\n");
    fprintf(html, "    background-clip: text;\n");
    fprintf(html, "}\n");
    fprintf(html, ".loading {\n");
    fprintf(html, "    color: #9ca3af;\n");
    fprintf(html, "    font-style: italic;\n");
    fprintf(html, "    padding: 20px;\n");
    fprintf(html, "    text-align: center;\n");
    fprintf(html, "}\n");
    fprintf(html, "</style>\n");  
    fprintf(html, "</head>\n<body>\n");
    fprintf(html, "<div class=\"page-header\">\n");
    fprintf(html, "<div class=\"header2\">\n");
fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
fprintf(html, "<h1>Three-Address Code</h1>\n");
fprintf(html, "<div class=\"toggle-container\">\n");
fprintf(html, "<span class=\"toggle-label\">Code View:</span>\n");
fprintf(html, "<span class=\"toggle-status unoptimized\" id=\"toggleStatus\">Unoptimized</span>\n");
fprintf(html, "<label class=\"toggle-switch\">\n");
fprintf(html, "<input type=\"checkbox\" id=\"codeToggle\">\n");
fprintf(html, "<span class=\"slider\"></span>\n");
fprintf(html, "</label>\n");
fprintf(html, "</div>\n");
fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"code-viewer\" id=\"codeViewer\">\n");
    fprintf(html, "<div class=\"loading\">Loading TAC code...</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<script>\n");
    fprintf(html, "let unoptimizedCode = [];\n");
    fprintf(html, "let optimizedCode = [];\n");
    fprintf(html, "let isLoaded = false;\n");
    fprintf(html, "const codeViewer = document.getElementById('codeViewer');\n");
    fprintf(html, "const codeToggle = document.getElementById('codeToggle');\n");
    fprintf(html, "const toggleStatus = document.getElementById('toggleStatus');\n");  
    fprintf(html, "async function loadTACFiles() {\n");
    fprintf(html, "    try {\n");
    fprintf(html, "        const unoptResponse = await fetch('unopt.tac');\n");
    fprintf(html, "        if (unoptResponse.ok) {\n");
    fprintf(html, "            const unoptText = await unoptResponse.text();\n");
    fprintf(html, "            unoptimizedCode = unoptText.trim().split('\\n').filter(line => line.trim() !== '');\n");
    fprintf(html, "        }\n");
    fprintf(html, "        const optResponse = await fetch('optimized.tac');\n");
    fprintf(html, "        if (optResponse.ok) {\n");
    fprintf(html, "            const optText = await optResponse.text();\n");
    fprintf(html, "            optimizedCode = optText.trim().split('\\n').filter(line => line.trim() !== '');\n");
    fprintf(html, "        }\n");
    fprintf(html, "        isLoaded = true;\n");
    fprintf(html, "        displayCode(unoptimizedCode, false);\n");
    fprintf(html, "    } catch (error) {\n");
    fprintf(html, "        console.error('Error loading TAC files:', error);\n");
    fprintf(html, "        codeViewer.innerHTML = '<div style=\"color: #ff6b6b; padding: 20px; text-align: center;\">Error loading TAC files</div>';\n");
    fprintf(html, "    }\n");
    fprintf(html, "}\n");    
    fprintf(html, "function displayCode(codeArray, isOptimized) {\n");
    fprintf(html, "    codeViewer.innerHTML = '';\n");
    fprintf(html, "    if (!codeArray || codeArray.length === 0) {\n");
    fprintf(html, "        codeViewer.innerHTML = '<div style=\"color: #ff6b6b; padding: 20px;\">No code to display</div>';\n");
    fprintf(html, "        return;\n");
    fprintf(html, "    }\n");
    fprintf(html, "    codeArray.forEach(line => {\n");
    fprintf(html, "        const span = document.createElement('span');\n");
    fprintf(html, "        span.className = 'code-line';\n");
    fprintf(html, "        if (isOptimized && (line.includes('// DEAD') || line.includes('//DEAD'))) {\n");
    fprintf(html, "            span.classList.add('dead');\n");
    fprintf(html, "        }\n");
    fprintf(html, "        if (line.trim().startsWith('//')) {\n");
    fprintf(html, "            span.classList.add('comment');\n");
    fprintf(html, "        }\n");
    fprintf(html, "        span.textContent = line;\n");
    fprintf(html, "        codeViewer.appendChild(span);\n");
    fprintf(html, "    });\n");
    fprintf(html, "}\n");  
    fprintf(html, "codeToggle.addEventListener('change', function() {\n");
    fprintf(html, "    if (!isLoaded) return;\n");
    fprintf(html, "    if (this.checked) {\n");
    fprintf(html, "        displayCode(optimizedCode, true);\n");
    fprintf(html, "        toggleStatus.textContent = 'Optimized';\n");
    fprintf(html, "        toggleStatus.classList.remove('unoptimized');\n");
    fprintf(html, "    } else {\n");
    fprintf(html, "        displayCode(unoptimizedCode, false);\n");
    fprintf(html, "        toggleStatus.textContent = 'Unoptimized';\n");
    fprintf(html, "        toggleStatus.classList.add('unoptimized');\n");
    fprintf(html, "    }\n");
    fprintf(html, "});\n"); 
    fprintf(html, "loadTACFiles();\n");
    fprintf(html, "</script>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateCFGPage() {
    FILE* html = fopen("cfg.html", "w");
        fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Control Flow - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "</head>\n<body>\n");  
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"page-header\">\n");
        fprintf(html, "<div class=\"header2\">\n");
   fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
    fprintf(html, "<h1> Control Flow Graphs</h1>\n");
    fprintf(html, "</div>\n");
        fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"toolbar\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-container\">\n");
    fprintf(html, "<div class=\"zoom-controls\">\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('cfg', -0.1)\">−</button>\n");
    fprintf(html, "<span class=\"zoom-level\" id=\"cfgZoomLevel\">100%%</span>\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('cfg', 0.1)\">+</button>\n");
    fprintf(html, "<button class=\"zoom-btn \" onclick=\"resetZoom('cfg')\">⟲</button>\n");
    fprintf(html, "<button class=\"zoom-btn fullscreen-btn\" onclick=\"openFullscreen('cfg')\">⛶</button>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-wrapper\" id=\"cfgWrapper\" onmousedown=\"startPan(event, 'cfg')\">\n");
    fprintf(html, "<img id=\"cfgImage\" src=\"tac_flow.png\" alt=\"Control Flow Graph\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div id=\"fullscreenModal\" class=\"fullscreen-modal\"></div>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateBBPage() {
    FILE* html = fopen("bsb.html", "w");
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Control Flow - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "</head>\n<body>\n");  
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"page-header\">\n");
        fprintf(html, "<div class=\"header2\">\n");
   fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
    fprintf(html, "<h1> Control Flow Graphs with Basic Blocks</h1>\n");
    fprintf(html, "</div>\n");
        fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"toolbar\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-container\">\n");
    fprintf(html, "<div class=\"zoom-controls\">\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('blocks', -0.1)\">−</button>\n");
    fprintf(html, "<span class=\"zoom-level\" id=\"blocksZoomLevel\">100%%</span>\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('blocks', 0.1)\">+</button>\n");
    fprintf(html, "<button class=\"zoom-btn \" onclick=\"resetZoom('blocks')\">⟲</button>\n");
    fprintf(html, "<button class=\"zoom-btn fullscreen-btn\" onclick=\"openFullscreen('blocks')\">⛶</button>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-wrapper\" id=\"blocksWrapper\" onmousedown=\"startPan(event, 'blocks')\">\n");
    fprintf(html, "<img id=\"blocksImage\" src=\"tac_flow_blocks.png\" alt=\"Basic Blocks CFG\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"stats-section\">\n");
    fprintf(html, "<h3>Basic Block Statistics</h3>\n");
    fprintf(html, "<table>\n");
    fprintf(html, "<tr><th>Block ID</th><th>Start Line</th><th>End Line</th><th>Instructions</th></tr>\n");  
    BasicBlock* bb = blocks;
    while (bb) {
        int inst_count = 0;
        for (int i = bb->start_line; i <= bb->end_line && i < code; i++) {
            if (strstr(imcode[i], "// DEAD") == NULL) inst_count++;
        }
        fprintf(html, "<tr><td>%d</td><td>%d</td><td>%d</td><td>%d</td></tr>\n",
                bb->block_id, bb->start_line, bb->end_line, inst_count);
        bb = bb->next;
    }
    fprintf(html, "</table>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n"); 
    fprintf(html, "</div>\n");
    fprintf(html, "<div id=\"fullscreenModal\" class=\"fullscreen-modal\"></div>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateCallGraphPage() {
    FILE* html = fopen("callgraph.html", "w");
 fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Control Flow - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "</head>\n<body>\n");  
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"page-header\">\n");
        fprintf(html, "<div class=\"header2\">\n");
   fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
    fprintf(html, "<h1> Function Call Graphs</h1>\n");
    fprintf(html, "</div>\n");
        fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"toolbar\">\n");
    fprintf(html, "</div>\n");   
    fprintf(html, "<div class=\"image-container\">\n");
    fprintf(html, "<div class=\"zoom-controls\">\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('callgraph', -0.1)\">−</button>\n");
    fprintf(html, "<span class=\"zoom-level\" id=\"callgraphZoomLevel\">100%%</span>\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('callgraph', 0.1)\">+</button>\n");
    fprintf(html, "<button class=\"zoom-btn \" onclick=\"resetZoom('callgraph')\">⟲</button>\n");
    fprintf(html, "<button class=\"zoom-btn fullscreen-btn\" onclick=\"openFullscreen('callgraph')\">⛶</button>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-wrapper\" id=\"callgraphWrapper\" onmousedown=\"startPan(event, 'callgraph')\">\n");
    fprintf(html, "<img id=\"callgraphImage\" src=\"call_graph.png\" alt=\"Call Graph\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div id=\"fullscreenModal\" class=\"fullscreen-modal\"></div>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateTokensPage() {
    FILE* html = fopen("tokens.html", "w");
    if (!html) return;
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Tokens - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "<style>\n");
    fprintf(html, ".tok-row    { display:flex; align-items:baseline; gap:0; padding:2px 0; }\n");
    fprintf(html, ".tok-row:hover { background: rgba(255,255,255,0.04); border-radius:4px; }\n");
    fprintf(html, ".col-loc    { color:#8b949e; font-size:0.85em; width:100px; flex-shrink:0; }\n");
    fprintf(html, ".col-type   { color:#79c0ff; font-weight:700;  width:210px; flex-shrink:0; }\n");
    fprintf(html, ".col-lexeme { color:#ffa657; }\n");
    fprintf(html, ".tok-header { display:flex; gap:0; padding:0 0 4px 0;\n");
    fprintf(html, "              border-bottom:1px solid rgba(41,227,60,0.2); margin-bottom:8px; }\n");
    fprintf(html, ".hdr-loc    { width:100px; flex-shrink:0; color:#6e7681; font-size:0.8em; font-weight:600; text-transform:uppercase; }\n");
    fprintf(html, ".hdr-type   { width:210px; flex-shrink:0; color:#6e7681; font-size:0.8em; font-weight:600; text-transform:uppercase; }\n");
    fprintf(html, ".hdr-lexeme { color:#6e7681; font-size:0.8em; font-weight:600; text-transform:uppercase; }\n");
    fprintf(html, ".tok-sep    { display:none; }\n");
    fprintf(html, ".search-bar { display:flex; gap:10px; margin-bottom:16px; }\n");
    fprintf(html, ".search-bar input { flex:1; background:#111827;\n");
    fprintf(html, "    border:1px solid rgba(41,227,60,0.2); color:#f3f4f6;\n");
    fprintf(html, "    border-radius:8px; padding:10px 16px; font-size:14px; outline:none; }\n");
    fprintf(html, ".search-bar input:focus { border-color:rgba(41,227,60,0.6); }\n");
    fprintf(html, ".search-bar input::placeholder { color:#4b5563; }\n");
    fprintf(html, ".tok-stats  { display:flex; gap:20px; margin-bottom:16px; flex-wrap:wrap; }\n");
    fprintf(html, ".tok-stat   { background:#111827; border:1px solid rgba(41,227,60,0.2);\n");
    fprintf(html, "              border-radius:8px; padding:10px 20px; text-align:center; }\n");
    fprintf(html, ".tok-stat .num { font-size:1.6em; font-weight:700;\n");
    fprintf(html, "    background:linear-gradient(90deg,rgba(97,215,101,1) 0%%,rgba(225,255,64,1) 100%%);\n");
    fprintf(html, "    -webkit-background-clip:text; -webkit-text-fill-color:transparent;\n");
    fprintf(html, "    background-clip:text; }\n");
    fprintf(html, ".tok-stat .lbl { color:#9ca3af; font-size:0.8em; margin-top:2px; }\n");
    fprintf(html, ".loading { color:#9ca3af; font-style:italic; padding:20px; text-align:center; }\n");
    fprintf(html, "</style>\n");
    fprintf(html, "</head>\n<body>\n");
    fprintf(html, "<div class=\"page-header\">\n");
    fprintf(html, "<div class=\"header2\">\n");
    fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
    fprintf(html, "<h1>Lexical Tokens</h1>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"tok-stats\">\n");
    fprintf(html, "<div class=\"tok-stat\"><div class=\"num\" id=\"totalTokens\">-</div><div class=\"lbl\">Total Tokens</div></div>\n");
    fprintf(html, "<div class=\"tok-stat\"><div class=\"num\" id=\"uniqueTypes\">-</div><div class=\"lbl\">Unique Types</div></div>\n");
    fprintf(html, "<div class=\"tok-stat\"><div class=\"num\" id=\"lineCount\">-</div><div class=\"lbl\">Source Lines</div></div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"search-bar\">\n");
    fprintf(html, "<input type=\"text\" id=\"tokenSearch\" placeholder=\"Search tokens by type or value...\" oninput=\"filterTokens()\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"tok-header\">\n");
    fprintf(html, "  <span class=\"hdr-loc\">Line:Col</span>\n");
    fprintf(html, "  <span class=\"hdr-type\">Token Type</span>\n");
    fprintf(html, "  <span class=\"hdr-lexeme\">Lexeme</span>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"code-viewer\" id=\"tokenViewer\">\n");
    fprintf(html, "<div class=\"loading\">Loading tokens.txt...</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n"); 
    fprintf(html, "<script>\n");
    fprintf(html, "let allTokenLines = [];\n");
    fprintf(html, "const viewer = document.getElementById('tokenViewer');\n");
    fprintf(html, "async function loadTokens() {\n");
    fprintf(html, "    try {\n");
    fprintf(html, "        const r = await fetch('tokens.txt');\n");
    fprintf(html, "        if (!r.ok) throw new Error('tokens.txt not found');\n");
    fprintf(html, "        const text = await r.text();\n");
    fprintf(html, "        allTokenLines = text.split('\\n').filter(l => {\n");
    fprintf(html, "            const t = l.trim();\n");
    fprintf(html, "            return t !== '' && !t.startsWith('----------') && !t.startsWith('[LINE:COL]');\n");
    fprintf(html, "        });\n");
    fprintf(html, "        updateStats(allTokenLines);\n");
    fprintf(html, "        renderTokens(allTokenLines);\n");
    fprintf(html, "    } catch(err) {\n");
    fprintf(html, "        viewer.innerHTML = '<div style=\"color:#ff6b6b;padding:20px;text-align:center;\">'\n");
    fprintf(html, "            + 'Error: ' + err.message + '</div>';\n");
    fprintf(html, "    }\n");
    fprintf(html, "}\n");
    fprintf(html, "function updateStats(lines) {\n");
    fprintf(html, "    const types = new Set();\n");
    fprintf(html, "    let maxLine = 0;\n");
    fprintf(html, "    lines.forEach(l => {\n");
    fprintf(html, "        const m = l.match(/^\\[(\\d+):(\\d+)\\]\\s+(\\S+)/);\n");
    fprintf(html, "        if (m) {\n");
    fprintf(html, "            types.add(m[3]);\n");
    fprintf(html, "            const ln = parseInt(m[1]);\n");
    fprintf(html, "            if (ln > maxLine) maxLine = ln;\n");
    fprintf(html, "        }\n");
    fprintf(html, "    });\n");
    fprintf(html, "    document.getElementById('totalTokens').textContent = lines.length;\n");
    fprintf(html, "    document.getElementById('uniqueTypes').textContent = types.size;\n");
    fprintf(html, "    document.getElementById('lineCount').textContent = maxLine || '-';\n");
    fprintf(html, "}\n");
    fprintf(html, "function renderTokens(lines) {\n");
    fprintf(html, "    viewer.innerHTML = '';\n");
    fprintf(html, "    const q = document.getElementById('tokenSearch').value.toLowerCase();\n");
    fprintf(html, "    lines.forEach(line => {\n");
    fprintf(html, "        if (q && !line.toLowerCase().includes(q)) return;\n");
    fprintf(html, "        const m = line.match(/^(\\[\\d+:\\d+\\])\\s+(\\S+)\\s+(.*)$/);\n");
    fprintf(html, "        const row = document.createElement('div');\n");
    fprintf(html, "        row.className = 'tok-row';\n");
    fprintf(html, "        if (m) {\n");
    fprintf(html, "            row.innerHTML =\n");
    fprintf(html, "                '<span class=\"col-loc\">'    + escHtml(m[1]) + '</span>'\n");
    fprintf(html, "              + '<span class=\"col-type\">'   + escHtml(m[2]) + '</span>'\n");
    fprintf(html, "              + '<span class=\"col-lexeme\">' + escHtml(m[3]) + '</span>';\n");
    fprintf(html, "        } else {\n");
    fprintf(html, "            row.textContent = line;\n");
    fprintf(html, "        }\n");
    fprintf(html, "        viewer.appendChild(row);\n");
    fprintf(html, "    });\n");
    fprintf(html, "    if (viewer.children.length === 0)\n");
    fprintf(html, "        viewer.innerHTML = '<div style=\"color:#9ca3af;padding:20px;\">No matching tokens.</div>';\n");
    fprintf(html, "}\n");
    fprintf(html, "function filterTokens() { renderTokens(allTokenLines); }\n");
    fprintf(html, "function escHtml(s) {\n");
    fprintf(html, "    return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');\n");
    fprintf(html, "}\n");
    fprintf(html, "loadTokens();\n");
    fprintf(html, "</script>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateSourcePage() {
    FILE* html = fopen("source.html", "w");
    if (!html) return;
    char* source = NULL;
    long  file_size = 0;
    if (input_filename[0] != '\0') {
        FILE* src = fopen(input_filename, "r");
        if (src) {
            fseek(src, 0, SEEK_END);
            file_size = ftell(src);
            fseek(src, 0, SEEK_SET);
            source = (char*)malloc(file_size + 1);
            if (source) {
                fread(source, 1, file_size, src);
                source[file_size] = '\0';
            }
            fclose(src);
        }
    }
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Source Code - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "</head>\n<body>\n");
    fprintf(html, "<div class=\"page-header\">\n");
    fprintf(html, "<div class=\"header2\">\n");
    fprintf(html, "<a href=\"index.html\" class=\"back-btn\">&#8678; Back</a>\n");
    fprintf(html, "<h1>Source Code</h1>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"code-viewer\">\n");
    fprintf(html, "<pre>\n");
    if (source && file_size > 0) {
        for (const char* p = source; *p; p++) {
            if      (*p == '&')  fprintf(html, "&amp;");
            else if (*p == '<')  fprintf(html, "&lt;");
            else if (*p == '>')  fprintf(html, "&gt;");
            else                 fputc(*p, html);
        }
    } else {
        fprintf(html, "No source file found.");
    }
    fprintf(html, "</pre>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
    if (source) free(source);
}
void generateSymbolsPage() {
    FILE* html = fopen("symbols.html", "w");
  fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Control Flow - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "</head>\n<body>\n");  
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"page-header\">\n");
        fprintf(html, "<div class=\"header2\">\n");
   fprintf(html, "<a href=\"index.html\" class=\"back-btn\">⬅ Back</a>\n");
    fprintf(html, "<h1> Symbol Table and Scope Views </h1>\n");
    fprintf(html, "</div>\n");
        fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"toolbar\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-container\" style=\"margin-top: 30px;\">\n");
    fprintf(html, "<div class=\"zoom-controls\">\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('symbols', -0.1)\">−</button>\n");
    fprintf(html, "<span class=\"zoom-level\" id=\"symbolsZoomLevel\">100%%</span>\n");
    fprintf(html, "<button class=\"zoom-btn\" onclick=\"zoomImage('symbols', 0.1)\">+</button>\n");
    fprintf(html, "<button class=\"zoom-btn \" onclick=\"resetZoom('symbols')\">⟲</button>\n");
    fprintf(html, "<button class=\"zoom-btn fullscreen-btn\" onclick=\"openFullscreen('symbols')\">⛶</button>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"image-wrapper\" id=\"symbolsWrapper\" onmousedown=\"startPan(event, 'symbols')\">\n");
    fprintf(html, "<img id=\"symbolsImage\" src=\"symbol_table.png\" alt=\"Symbol Table Graph\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
  for (int i = 0; i < env_count; i++) {
        fprintf(html, "<div class=\"scope-section\">\n");
        fprintf(html, "<h3>Scope %d</h3>\n", i);
        fprintf(html, "<table>\n");
        fprintf(html, "<tr><th>Variable</th><th>Type</th><th>Declared Line</th><th>Dimensions</th></tr>\n");
        Table* table = envs[i]->table;
        for (int j = 0; j < table->size; j++) {
            TableEntry* entry = table->buckets[j];
            while (entry) {
                char dims[100] = "-";
                if (entry->value->dim_count > 0) {
                    strcpy(dims, "[");
                    for (int d = 0; d < entry->value->dim_count; d++) {
                        char temp[20];
                        sprintf(temp, "%d", entry->value->dimensions[d]);
                        strcat(dims, temp);
                        if (d < entry->value->dim_count - 1) strcat(dims, "][");
                    }
                    strcat(dims, "]");
                }
                fprintf(html, "<tr><td>%s</td><td>%s</td><td>%d</td><td>%s</td></tr>\n",
        entry->value->name, entry->value->type,
        entry->value->decl_line, dims);
                entry = entry->next;
            }
        }
        fprintf(html, "</table>\n");
        fprintf(html, "</div>\n");
    }
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div id=\"fullscreenModal\" class=\"fullscreen-modal\"></div>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateQuadruplesPage() {
    FILE *qf = fopen("quadruples.txt", "r");
    if (!qf) {
        fprintf(stderr, "Error: could not open quadruples.txt\n");
        return;
    }
    typedef struct { char op[100]; char arg1[200]; char arg2[200]; char res[200]; } Quad;
    Quad *quads = NULL;
    int total_quads = 0, cap = 0;
    char line[1024];
    while (fgets(line, sizeof(line), qf)) {
        if (line[0] == '=' || line[0] == '\n' || line[0] == '\r') continue;
        if (strstr(line, "op") && strstr(line, "arg1"))            continue;
        if (strstr(line, "----"))                                   continue;
        if (strstr(line, "Total quadruples:"))                      continue;
        int idx;
        char op[100], arg1[200], arg2[200], res[200];
        if (sscanf(line, " %d %99s %199s %199s %199s",
                   &idx, op, arg1, arg2, res) < 2) continue;
        if (total_quads >= cap) {
            cap = cap ? cap * 2 : 64;
            quads = realloc(quads, cap * sizeof(Quad));
        }
        strncpy(quads[total_quads].op,   op,   99);
        strncpy(quads[total_quads].arg1, arg1, 199);
        strncpy(quads[total_quads].arg2, arg2, 199);
        strncpy(quads[total_quads].res,  res,  199);
        total_quads++;
    }
    fclose(qf);
    FILE *html = fopen("quadruples.html", "w");
    if (!html) { free(quads); return; }
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Quadruples - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "<style>\n");
    fprintf(html, ".quad-table { width:100%%; border-collapse:collapse; margin-top:8px; font-size:14px; }\n");
    fprintf(html, ".quad-table thead th {\n");
    fprintf(html, "    background:#0d1117;\n");
    fprintf(html, "    color:#6e7681;\n");
    fprintf(html, "    font-size:0.8em; font-weight:600; text-transform:uppercase; letter-spacing:0.05em;\n");
    fprintf(html, "    padding:10px 16px;\n");
    fprintf(html, "    border-bottom:1px solid rgba(41,227,60,0.2);\n");
    fprintf(html, "    position:sticky; top:0; z-index:2;\n");
    fprintf(html, "    text-align:left;\n");
    fprintf(html, "}\n");
    fprintf(html, ".quad-table td {\n");
    fprintf(html, "    padding:9px 16px;\n");
    fprintf(html, "    border-bottom:1px solid rgba(255,255,255,0.04);\n");
    fprintf(html, "    vertical-align:middle;\n");
    fprintf(html, "    color:#ffffff;\n");
    fprintf(html, "}\n");
    fprintf(html, ".quad-table tbody tr:hover td { background:rgba(41,227,60,0.05); }\n");
    fprintf(html, ".idx-col  { color:#79c0ff !important; width:56px; text-align:right; padding-right:20px; font-size:0.85em; }\n");
    fprintf(html, ".op-col   { color:#ffa657 !important; font-weight:700; width:160px; }\n");
    fprintf(html, ".arg1-col { color:#ffffff !important; width:200px; }\n");
    fprintf(html, ".arg2-col { color:#ffffff !important; width:200px; }\n");
    fprintf(html, ".res-col  { color:#ffffff !important; font-weight:600; }\n");
    fprintf(html, ".comment-row td { color:#ffffff !important; font-style:italic; }\n");
    fprintf(html, ".label-row   td { color:#ffffff !important; font-weight:700; }\n");
    fprintf(html, ".search-bar { display:flex; gap:10px; margin-bottom:16px; }\n");
    fprintf(html, ".search-bar input { flex:1; background:#111827;\n");
    fprintf(html, "    border:1px solid rgba(41,227,60,0.2); color:#f3f4f6;\n");
    fprintf(html, "    border-radius:8px; padding:10px 16px; font-size:14px; outline:none; }\n");
    fprintf(html, ".search-bar input:focus { border-color:rgba(41,227,60,0.6); }\n");
    fprintf(html, ".search-bar input::placeholder { color:#4b5563; }\n");
    fprintf(html, ".quad-stats { display:flex; gap:20px; margin-bottom:16px; flex-wrap:wrap; }\n");
    fprintf(html, ".quad-stat  { background:#111827; border:1px solid rgba(41,227,60,0.2);\n");
    fprintf(html, "              border-radius:8px; padding:10px 20px; text-align:center; }\n");
    fprintf(html, ".quad-stat .num { font-size:1.6em; font-weight:700;\n");
    fprintf(html, "    background:linear-gradient(90deg,rgba(97,215,101,1) 0%%,rgba(225,255,64,1) 100%%);\n");
    fprintf(html, "    -webkit-background-clip:text; -webkit-text-fill-color:transparent;\n");
    fprintf(html, "    background-clip:text; }\n");
    fprintf(html, ".quad-stat .lbl { color:#9ca3af; font-size:0.8em; margin-top:2px; }\n");
    fprintf(html, "</style>\n");
    fprintf(html, "</head>\n<body>\n");
    fprintf(html, "<div class=\"page-header\">\n");
    fprintf(html, "<div class=\"header2\">\n");
    fprintf(html, "<a href=\"index.html\" class=\"back-btn\">&#8678; Back</a>\n");
    fprintf(html, "<h1>Quadruples Representation</h1>\n");
    fprintf(html, "</div>\n</div>\n");
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"quad-stats\">\n");
    fprintf(html, "<div class=\"quad-stat\"><div class=\"num\">%d</div><div class=\"lbl\">Total Quadruples</div></div>\n", total_quads);
    fprintf(html, "<div class=\"quad-stat\"><div class=\"num\" id=\"visibleCount\">%d</div><div class=\"lbl\">Visible (after filter)</div></div>\n", total_quads);
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"search-bar\">\n");
    fprintf(html, "<input type=\"text\" id=\"quadSearch\" placeholder=\"Search by op, arg1, arg2 or result...\" oninput=\"filterQuads()\">\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div style=\"overflow-x:auto;overflow-y:auto;max-height:70vh;\">\n");
    fprintf(html, "<table class=\"quad-table\" id=\"quadTable\">\n");
    fprintf(html, "<thead><tr>\n");
    fprintf(html, "<th class=\"idx-col\">#</th>\n");
    fprintf(html, "<th>Op</th><th>Arg1</th><th>Arg2</th><th>Result</th>\n");
    fprintf(html, "</tr></thead>\n");
    fprintf(html, "<tbody id=\"quadBody\">\n");
    for (int i = 0; i < total_quads; i++) {
        const char *op   = quads[i].op;
        const char *arg1 = quads[i].arg1;
        const char *arg2 = quads[i].arg2;
        const char *res  = quads[i].res;
        const char *rowcls = "";
        if (strncmp(op, "//", 2) == 0)    rowcls = "comment-row";
        else if (strcmp(op, "label") == 0) rowcls = "label-row";
        fprintf(html,
            "<tr class=\"%s\" data-search=\"%s %s %s %s\">\n"
            "<td class=\"idx-col\">%d</td>\n"
            "<td class=\"op-col\">%s</td>\n"
            "<td class=\"arg1-col\">%s</td>\n"
            "<td class=\"arg2-col\">%s</td>\n"
            "<td class=\"res-col\">%s</td>\n"
            "</tr>\n",
            rowcls, op, arg1, arg2, res,
            i,
            op[0]   ? op   : "_",
            arg1[0] ? arg1 : "_",
            arg2[0] ? arg2 : "_",
            res[0]  ? res  : "_");
    }
    fprintf(html, "</tbody>\n</table>\n</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<script>\n");
    fprintf(html, "function filterQuads() {\n");
    fprintf(html, "    const q = document.getElementById('quadSearch').value.toLowerCase();\n");
    fprintf(html, "    const rows = document.querySelectorAll('#quadBody tr');\n");
    fprintf(html, "    let vis = 0;\n");
    fprintf(html, "    rows.forEach(r => {\n");
    fprintf(html, "        const match = !q || r.dataset.search.toLowerCase().includes(q);\n");
    fprintf(html, "        r.style.display = match ? '' : 'none';\n");
    fprintf(html, "        if (match) vis++;\n");
    fprintf(html, "    });\n");
    fprintf(html, "    document.getElementById('visibleCount').textContent = vis;\n");
    fprintf(html, "}\n");
    fprintf(html, "</script>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
    free(quads);
}
void generateOptimizationReportPage() {
    FILE* html = fopen("optreport.html", "w");
    if (!html) return;
    fprintf(html, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(html, "<meta charset=\"UTF-8\">\n");
    fprintf(html, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(html, "<title>Optimization Report - Compiler Dashboard</title>\n");
    fprintf(html, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(html, "<style>\n");
    fprintf(html, ".opt-stats { display:flex; gap:20px; margin-bottom:24px; flex-wrap:wrap; }\n");
    fprintf(html, ".opt-stat  { background:#111827; border:1px solid rgba(41,227,60,0.2);\n");
    fprintf(html, "             border-radius:8px; padding:10px 20px; text-align:center; }\n");
    fprintf(html, ".opt-stat .num { font-size:1.6em; font-weight:700;\n");
    fprintf(html, "    background:linear-gradient(90deg,rgba(97,215,101,1) 0%%,rgba(225,255,64,1) 100%%);\n");
    fprintf(html, "    -webkit-background-clip:text; -webkit-text-fill-color:transparent;\n");
    fprintf(html, "    background-clip:text; }\n");
    fprintf(html, ".opt-stat .lbl { color:#9ca3af; font-size:0.8em; margin-top:2px; }\n");
    fprintf(html, ".opt-table { width:100%%; border-collapse:collapse; margin-top:8px; font-size:14px; }\n");
    fprintf(html, ".opt-table thead th {\n");
    fprintf(html, "    color:#6e7681;\n");
    fprintf(html, "    font-size:0.8em; font-weight:600; text-transform:uppercase; letter-spacing:0.05em;\n");
    fprintf(html, "    padding:10px 16px;\n");
    fprintf(html, "    border-bottom:1px solid rgba(41,227,60,0.2);\n");
    fprintf(html, "    position:sticky; top:0; z-index:2;\n");
    fprintf(html, "    text-align:left;\n");
    fprintf(html, "}\n");
    fprintf(html, ".opt-table thead th.count-th { text-align:right; }\n");
    fprintf(html, ".opt-table td {\n");
    fprintf(html, "    padding:9px 16px;\n");
    fprintf(html, "    border-bottom:1px solid rgba(255,255,255,0.04);\n");
    fprintf(html, "    vertical-align:middle;\n");
    fprintf(html, "    color:#e6edf3;\n");
    fprintf(html, "}\n");
    fprintf(html, ".opt-table tbody tr:hover td { background:rgba(41,227,60,0.05); }\n");
    fprintf(html, ".pass-col   { color:#79c0ff !important; font-weight:700; }\n");
    fprintf(html, ".count-col  { color:#ffa657!important; font-weight:700; text-align:right; }\n");
    fprintf(html, ".effect-col { color:#ffffff !important; }\n");
    fprintf(html, ".zero-row td { opacity:1; }\n");
    fprintf(html, ".loading  { color:#9ca3af; font-style:italic; padding:20px; text-align:center; }\n");
    fprintf(html, "</style>\n");
    fprintf(html, "</head>\n<body>\n");
    fprintf(html, "<div class=\"page-header\">\n");
    fprintf(html, "<div class=\"header2\">\n");
    fprintf(html, "<a href=\"index.html\" class=\"back-btn\">&#8678; Back</a>\n");
    fprintf(html, "<h1>Optimization Report</h1>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div class=\"container\">\n");
    fprintf(html, "<div class=\"opt-stats\" id=\"optStats\">\n");
    fprintf(html, "<div class=\"opt-stat\"><div class=\"num\" id=\"statBefore\">-</div><div class=\"lbl\">Before</div></div>\n");
    fprintf(html, "<div class=\"opt-stat\"><div class=\"num\" id=\"statAfter\">-</div><div class=\"lbl\">After</div></div>\n");
    fprintf(html, "<div class=\"opt-stat\"><div class=\"num\" id=\"statElim\">-</div><div class=\"lbl\">Eliminated</div></div>\n");
    fprintf(html, "<div class=\"opt-stat\"><div class=\"num\" id=\"statPct\">-</div><div class=\"lbl\">Reduction</div></div>\n");
    fprintf(html, "</div>\n");
    fprintf(html, "<div style=\"overflow-x:auto;overflow-y:auto;max-height:65vh;\">\n");
    fprintf(html, "<table class=\"opt-table\" id=\"optTable\">\n");
    fprintf(html, "<thead><tr>\n");
    fprintf(html, "<th>Pass</th>\n");
    fprintf(html, "<th class=\"count-th\">Instances</th>\n");
    fprintf(html, "<th>Effect</th>\n");
    fprintf(html, "</tr></thead>\n");
    fprintf(html, "<tbody id=\"optBody\"><tr><td colspan=\"3\"><div class=\"loading\">Loading optimization_report.txt...</div></td></tr></tbody>\n");
    fprintf(html, "</table>\n</div>\n");
    fprintf(html, "</div>\n"); 
    fprintf(html, "<script>\n");
    fprintf(html, "async function loadReport() {\n");
    fprintf(html, "  try {\n");
    fprintf(html, "    const r = await fetch('optimization_report.txt');\n");
    fprintf(html, "    if (!r.ok) throw new Error('optimization_report.txt not found');\n");
    fprintf(html, "    const txt = await r.text();\n");
    fprintf(html, "    parseAndRender(txt);\n");
    fprintf(html, "  } catch(e) {\n");
    fprintf(html, "    document.getElementById('optBody').innerHTML =\n");
    fprintf(html, "      '<tr><td colspan=\"3\"><div style=\"color:#ff6b6b;padding:20px;text-align:center;\">Error: ' + e.message + '</div></td></tr>';\n");
    fprintf(html, "  }\n");
    fprintf(html, "}\n");
    fprintf(html, "function parseAndRender(txt) {\n");
    fprintf(html, "  const lines = txt.split('\\n');\n");
    fprintf(html, "  let before=0, after=0, elim=0, pct=0;\n");
    fprintf(html, "  const rows = [];\n");
    fprintf(html, "  let maxCount = 1;\n");
    fprintf(html, "  lines.forEach(l => {\n");
    fprintf(html, "    const m1 = l.match(/TAC instructions before.*?:\\s*(\\d+)/);\n");
    fprintf(html, "    if (m1) before = parseInt(m1[1]);\n");
    fprintf(html, "    const m2 = l.match(/TAC instructions after.*?:\\s*(\\d+)/);\n");
    fprintf(html, "    if (m2) after = parseInt(m2[1]);\n");
    fprintf(html, "    const m3 = l.match(/Instructions eliminated.*?:\\s*(\\d+)/);\n");
    fprintf(html, "    if (m3) elim = parseInt(m3[1]);\n");
    fprintf(html, "    const m4 = l.match(/Code size reduction.*?:\\s*([\\d.]+)/);\n");
    fprintf(html, "    if (m4) pct = parseFloat(m4[1]);\n");
    fprintf(html, "    const mr = l.match(/^\\s{2}(.*?)\\|\\s*(\\d+)\\s*\\|\\s*(.+)$/);\n");
    fprintf(html, "    if (mr) {\n");
    fprintf(html, "      const cnt = parseInt(mr[2]);\n");
    fprintf(html, "      if (cnt > maxCount) maxCount = cnt;\n");
    fprintf(html, "      rows.push({ pass: mr[1].trim(), count: cnt, effect: mr[3].trim() });\n");
    fprintf(html, "    }\n");
    fprintf(html, "  });\n");
    fprintf(html, "  document.getElementById('statBefore').textContent = before;\n");
    fprintf(html, "  document.getElementById('statAfter').textContent  = after;\n");
    fprintf(html, "  document.getElementById('statElim').textContent   = elim;\n");
    fprintf(html, "  document.getElementById('statPct').textContent    = pct.toFixed(1) + '%%';\n");
    fprintf(html, "  document.getElementById('optBody').innerHTML = rows.map(r => {\n");
    fprintf(html, "    const rowcls = r.count === 0 ? 'zero-row' : '';\n");
    fprintf(html, "    return `<tr class='${rowcls}'>`\n");
    fprintf(html, "      + `<td class='pass-col'>${r.pass}</td>`\n");
    fprintf(html, "      + `<td class='count-col'>${r.count}</td>`\n");
    fprintf(html, "      + `<td class='effect-col'>${r.effect}</td>`\n");
    fprintf(html, "      + `</tr>`;\n");
    fprintf(html, "  }).join('');\n");
    fprintf(html, "}\n");
    fprintf(html, "loadReport();\n");
    fprintf(html, "</script>\n");
    fprintf(html, "<script src=\"script.js\"></script>\n");
    fprintf(html, "</body>\n</html>\n");
    fclose(html);
}
void generateInteractiveDashboard() {
    FILE* index = fopen("index.html", "w");
    fprintf(index, "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    fprintf(index, "<meta charset=\"UTF-8\">\n");
    fprintf(index, "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">\n");
    fprintf(index, "<title>Compiler Visualization Dashboard</title>\n");
    fprintf(index, "<link rel=\"stylesheet\" href=\"styles.css\">\n");
    fprintf(index, "</head>\n<body>\n"); 
    fprintf(index, "<div class=\"container\">\n");
    fprintf(index, "<div class=\"header\">\n");
    fprintf(index, "<h1>Compiler Dashboard </h1>\n");
fprintf(index, "<p>Visualize and analyze your program across every stage of compilation</p>\n");
    fprintf(index, "</div>\n");
fprintf(index, "<div class=\"stats\">\n");
fprintf(index, "<div class=\"stat-card\"><div class=\"number\">%d</div><div class=\"label\">TAC Instructions</div></div>\n", code);
fprintf(index, "<div class=\"stat-card\"><div class=\"number\">%d</div><div class=\"label\">Scopes</div></div>\n", env_count);
int func_count = 0;
Function* f = func_list;
while (f) { func_count++; f = f->next; }
fprintf(index, "<div class=\"stat-card\"><div class=\"number\">%d</div><div class=\"label\">Functions</div></div>\n", func_count);
fprintf(index, "<div class=\"stat-card\"><div class=\"number\">%d</div><div class=\"label\">Basic Blocks</div></div>\n", block_count);
fprintf(index, "<div class=\"stat-card\"><div class=\"number\">%d</div><div class=\"label\">Errors</div></div>\n", e);
fprintf(index, "</div>\n");
    fprintf(index, "<div class=\"nav-grid\" style=\"display:grid;grid-template-columns:repeat(5,1fr);gap:24px;margin-top:20px;\">\n");
    fprintf(index, "<a href=\"source.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">📄</div>\n");
    fprintf(index, "<h2>Source Code</h2>\n");
    fprintf(index, "<p>View the input source with syntax highlighting</p>\n");
    fprintf(index, "</a>\n");
       fprintf(index, "<a href=\"tokens.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">🔠</div>\n");
    fprintf(index, "<h2>Tokens</h2>\n");
    fprintf(index, "<p>Lexical tokens produced by the scanner</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"tac.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">📝</div>\n");
    fprintf(index, "<h2>TAC Code</h2>\n");
    fprintf(index, "<p>View three-address code with optimizations</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"cfg.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">🔀</div>\n");
    fprintf(index, "<h2>Control Flow</h2>\n");
    fprintf(index, "<p>Visualize program control flow graphs</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"bsb.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">🧱</div>\n");
    fprintf(index, "<h2>Basic Blocks</h2>\n");
    fprintf(index, "<p>Visualize control flow graphs using Basic Blocks</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"quadruples.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">🗂️</div>\n");
    fprintf(index, "<h2>Quadruples</h2>\n");
    fprintf(index, "<p>Quadruple representation of TAC instructions</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"callgraph.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">📞</div>\n");
    fprintf(index, "<h2>Call Graph</h2>\n");
    fprintf(index, "<p>Function call relationships & metrics</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"symbols.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">🔤</div>\n");
    fprintf(index, "<h2>Symbol Tables</h2>\n");
    fprintf(index, "<p>Variable scopes and storage layout</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"asm.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">⚙️</div>\n");
    fprintf(index, "<h2>Assembly</h2>\n");
    fprintf(index, "<p>RISC-V assembly code generated from TAC</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "<a href=\"optreport.html\" class=\"nav-card\">\n");
    fprintf(index, "<div class=\"icon\">📊</div>\n");
    fprintf(index, "<h2>Opt. Report</h2>\n");
    fprintf(index, "<p>Per-pass optimization breakdown & stats</p>\n");
    fprintf(index, "</a>\n");
    fprintf(index, "</div>\n"); 
    fprintf(index, "</div>\n");
    fprintf(index, "<script src=\"script.js\"></script>\n");
    fprintf(index, "</body>\n</html>\n");
    fclose(index);
    generateAllImages();
    generateSourcePage();
    generateTokensPage();
    generateTACPage();
    generateCFGPage();
    generateBBPage();
    generateCallGraphPage();
    generateSymbolsPage();
    generateAsmPage();
    generateQuadruplesPage();
    generateOptimizationReportPage();
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
        strncpy(input_filename, argv[1], sizeof(input_filename) - 1);
        fseek(f, 0, SEEK_END);
        long fsize = ftell(f);
        fseek(f, 0, SEEK_SET);
        char* raw = (char*)malloc(fsize + 2);
        if (!raw) { fclose(f); return 1; }
        fread(raw, 1, fsize, f);
        raw[fsize] = '\0';
        fclose(f);
        char* clean = (char*)malloc(fsize * 3 + 4);
        if (!clean) { free(raw); return 1; }
        int j = 0;
        for (int i = 0; i < (int)fsize; i++) {
            if (raw[i] == '\r') continue;              
            if (raw[i] == '$') {
                if (j > 0 && clean[j-1] != ' ' && clean[j-1] != '\t' && clean[j-1] != '\n')
                    clean[j++] = ' ';                  
                clean[j++] = '$';
                clean[j++] = ' ';                      
            } else {
                clean[j++] = raw[i];
            }
        }
        if (j == 0 || clean[j-1] != '\n') clean[j++] = '\n'; 
        clean[j] = '\0';
        free(raw);
        memset(imcode, 0, sizeof(imcode));
        yy_scan_string(clean);  
        yyparse();
        free(clean);
    }
remove("optimized.tac");
if (!e) {
    FILE* tac_file = fopen("optimized.tac", "w");
    if (tac_file) {
        for (int i = 0; i < code; i++)
            fprintf(tac_file, "%s", imcode[i]);
        fclose(tac_file);
    }
    write_symtab_json(); 
    generateInteractiveDashboard();
} else {
    FILE* tac_file = fopen("optimized.tac", "w");
    if (tac_file) {
        fprintf(tac_file, "# SEMANTIC_ERROR\n");
        fclose(tac_file);
    }
}
return e ? 1 : 0;   
}