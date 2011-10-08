// IDA2PAT for IDA 6.2 OSX 
// fixed a few things and ingtgrated crc16.cpp into it to work proper
// 8/10/2011 - Alexander Pick
//
//  Original Plugin:
//
//  IDB to PAT v1.0
//  Plugin module for IDA Pro v4.30/IDASDK430
//  J.C. Roberts <mercury@abac.com>
//
//
//  *   LICENSE/: Freeware / Public domain :-)
//
//  *   The CCITT CRC 16 code written by Ilfak Guilfanov (ig@datarescue.be> and
//      provided in the FLAIR Utilities v4.21 package. You will need the
//      "CRC16.CPP" file from this package in order to complile. Also portions
//      of the plugin originated from the MS VC++ skeleton provided with the 
//      IDA Pro SDK v4.30.
//
//  *   Portions were originally written by Quine (quine@blacksun.res.cmu.edu)
//      in his  IDV_2_SIG plugin. Quine's IDA Page at http://surf.to/quine_ida
//      I've tried to reach him at above address regarding the license of his
//      code but emails to that address bounce. As far as I know it was 
//      licensed as freeware but if I'm wrong I would like Quine to contact me.
//
//  *   See the "readme.txt" for further information.
//

#include <stdio.h>
#include <ida.hpp>
#include <idp.hpp>
#include <ua.hpp>
#include <auto.hpp>

#include <loader.hpp>
#include <kernwin.hpp>
#include <bytes.hpp>
#include <name.hpp>
#include <entry.hpp>
#include <funcs.hpp>
#include <expr.hpp>
#include <fpro.h>
#include <diskio.hpp>

#include <string.h>

// vector must be included first because of Rogue Wave STL
#include <vector>
#include <map>

// Minumum number of bytes a function needs in order to be patterned
#define MIN_SIG_LENGTH 10

// These things need to be shorts rather than #def or enum since
// AskUsingForm_c() requires shorts.

const short CHKBX_DO_NADA = 0x0000;     // Null for no boxes checked
const short CHKBX_DO_LIBS = 0x0001;     // Include library functions
const short CHKBX_DO_SUBS = 0x0002;     // Include Auto-Generated Names "sub_*"
const short CHKBX_NO_LIBS = 0x0004;     // Exclude library functions
const short CHKBX_DO_TEMP = 0x0008;     // Not used

const short RADIO_NON_FUNC = 0x0000;    // non auto-generated
const short RADIO_LIB_FUNC = 0x0001;    // library functions
const short RADIO_PUB_FUNC = 0x0002;    // exported functions
const short RADIO_ALL_FUNC = 0x0003;    // all functions
const short RADIO_USR_FUNC = 0x0004;    // user selected function

const short RADIO_IS_ERROR = -1;

// Structure for passing user options
typedef struct tagPATOPTION {
    short radio;
    short chkbx;
} PATOPTION;


#ifndef NOPROTO
// Source File: "crc16.cpp"
// prototype for CCITT CRC16 function
unsigned short crc16(unsigned char *,unsigned short);

// Source File: "idb2pat.cpp"
// prototype for the find_ref_loc() function.
ea_t find_ref_loc(ea_t, ea_t);

// prototype for the set varible bytes function.
void set_v_bytes (std::vector<bool>&, int, int);

// prototype for the make_pattern() function.
void make_pattern(func_t*, FILE*, PATOPTION*);

// prototype for the dialog
PATOPTION* opt_diaolg(PATOPTION*);

// prototype for get pattern file dialog.
FILE* get_pat_file(void);

// prototype for the primary run() function.
void run(int);

#endif

// crc16 from flair

#define POLY 0x8408

unsigned short local_crc16(unsigned char *data_p, size_t length)
{
    unsigned char i;
    unsigned int data;
    
    if ( length == 0 ) return 0;
    unsigned int crc = 0xFFFF;
    do
    {
        data = *data_p++;
        for ( i=0; i < 8; i++ )
        {
            if ( (crc ^ data) & 1 )
                crc = (crc >> 1) ^ POLY;
            else
                crc >>= 1;
            data >>= 1;
        }
    } while ( --length != 0 );
    
    crc = ~crc;
    data = crc;
    crc = (crc << 8) | ((data >> 8) & 0xff);
    return (unsigned short)(crc);
}

// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// Globals ;-)

//  Help strings
char comment[] = "This is the IDB_2_PAT plugin. It creates pattern files.";
char help[] = "This plugin creates pattern files from\n"
              "the functions defined in the disassembly.";

// This is the preferred name of the plugin module in the menu system
char wanted_name[] = "IDB_2_PAT Pattern Creation";

// This is the preferred hotkey for the plugin module
// The preferred hotkey may be overriden in plugins.cfg file
// Note: IDA won't tell you if the hotkey is not correct
//       It will just disable the hotkey.
char wanted_hotkey[] = "Ctrl-F12";

PATOPTION opt_stru;                     // User defined options structure
PATOPTION* opt_ptr = &opt_stru;         // umm... pointer to said structure


// Vars for Stats
long int g_skip_ctr = 0;          // Number of Skiped Function Counter
long int g_shrt_ctr = 0;          // Number of Functions too short for sig
long int g_libs_ctr = 0;          // Number of Library Function Counter
long int g_pubs_ctr = 0;          // Number of Public Function Counter
long int g_badf_ctr = 0;          // Number of Bad Functin Number Counter
long int g_badn_ctr = 0;          // Number of Bad Function Name Counter
long int g_badp_ctr = 0;          // Number of Bad Public Name Counter
long int g_badr_ctr = 0;          // Number of Bad Reference Name Counter
long int g_pats_ctr = 0;          // Number of Pattern Created

// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// FUNCTION: find_ref_loc
//
// this function finds the location of a reference within an instruction
// or a data item e.g.
//      .text:00401000  E8 FB 0F 00 00   call sub_402000
//
// find_ref_loc(0x401000, 0x402000) would return 0x401001
// it works for both segment relative and self-relative offsets
//
// NOTE:    All references are assumed to be 4 bytes long.
//          This is will be problematic for some processors.
//
ea_t find_ref_loc(ea_t item, ea_t _ref)
{
    ea_t i;
    if ( isCode(getFlags(item)) ) {
        decode_insn(item);
        if ( cmd.Operands[0].type == o_near ) {
            // we've got a self-relative reference
            _ref = _ref - (get_item_end(item));
        }
    }
    for ( i = item; i <= get_item_end(item)-4; i++) {
        if ( get_long(i) == _ref) {
            return i;
        }
    }
    return BADADDR;
}

// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// FUNCTON: set_v_bytes
//
// marks off bytes as variable
//
void set_v_bytes (std::vector<bool>& bv, int pos, int len=4) {
    for ( int i=0; i<len; i++ ) {
        bv[pos+i] = true;
    }
}



// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// FUNCTION: make_pattern
// this is what does the real work
//
void make_pattern(func_t* funcstru, FILE* fptr_pat, PATOPTION* opt_ptr)
{
    ea_t ea, ref_ea, ref_loc_ea, start_ea;
    int first_string = 0, alen = 0;
    int i = 0;
    int xoff = 0;
    unsigned char crc_data[256];
    ushort crc = 0;
    char buf[MAXNAMELEN+1];                 // Function Name Buffer
    char *name = &buf[0];                   // Function Name ptr
    char xbuf[MAXNAMELEN+1];                // Modified Name Buffer e.g. "FAKE_"
    char *xname = &xbuf[0];                 // Modified Name ptr

    unsigned long len;                              // Function Length
    flags_t mflags;                         // ulong for ea flags data

    start_ea = funcstru->startEA;           // Get Function Start EA
    len = (funcstru->endEA) - start_ea;     // Get Function Length


    typedef std::map<ea_t, ea_t, std::less<ea_t> > ref_map;
    ref_map refs;

    typedef std::vector<bool> bool_vec;
    bool_vec v_bytes(len);

    std::vector<ea_t> qpublics;


// PART #1  Get the pubs and refernces
    ea = start_ea;
    while ( ea - start_ea < len ) {
        mflags = getFlags(ea);

        // load up the publics vector
        if (opt_ptr->chkbx & CHKBX_DO_SUBS) {
            // Does the current byte have ANY name (includes "sub_" "loc_" etc.)
            if ( has_any_name(mflags) ) {
                name = get_true_name(BADADDR, ea, buf, MAXNAMELEN);

                if (name != NULL) {
                    // Only include the "sub_"names (exclude "loc_" etc.)
                    if ( strstr(name, "sub_") ) {
                        qpublics.push_back(ea);
                    // Does the current byte have non-trivial (non-dummy) name?
                    } else if ( has_name(mflags) ) {
                        qpublics.push_back(ea);
                    }
                }
            }
        } else {
            // Does the current byte have non-trivial (non-dummy) name?
            if ( has_name(mflags) ) {
                qpublics.push_back(ea);
            }
        }

        // load up refernces map
        if ((ref_ea = get_first_dref_from(ea)) != BADADDR) {
            // a data location is referenced
            ref_loc_ea = find_ref_loc(ea, ref_ea);

            if (ref_loc_ea != BADADDR) {                        // Error Check
                set_v_bytes(v_bytes, ref_loc_ea-start_ea);
                refs[ref_loc_ea] = ref_ea;
            }

            // check if there is a second data location ref'd
            if ( (ref_ea = get_next_dref_from(ea, ref_ea)) != BADADDR ) {
                ref_loc_ea = find_ref_loc(ea, ref_ea);

                if (ref_loc_ea != BADADDR) {                    // Error Check
                    set_v_bytes(v_bytes, ref_loc_ea-start_ea);
                    refs[ref_loc_ea] = ref_ea;
                }
            }

        } else {
            // do we have a code ref?
            if ( (ref_ea = get_first_fcref_from(ea)) != BADADDR ) {
                // if so, make sure it is outside of function
                if ( (ref_ea < start_ea) || (ref_ea >= start_ea+len) ) {

                    ref_loc_ea = find_ref_loc(ea, ref_ea);
                    if (ref_loc_ea != BADADDR) {                // Error Check
                        set_v_bytes(v_bytes, ref_loc_ea-start_ea);
                        refs[ref_loc_ea] = ref_ea;
                    }
                }
            }
        }
        ea = next_not_tail(ea);
    }

// PART #2
    // write out the first string of bytes,
    // making sure not to go past the end of the function
    first_string = (len < 32 ? len : 32);
    for ( i = 0; i<first_string; i++ ) {
        if ( v_bytes[i] ) {
            qfprintf(fptr_pat, "..");
        } else {
            qfprintf(fptr_pat, "%02X", get_byte(start_ea+i));
        }
    }

// PART #3
    // fill in anything less than 32
    for ( i = 0; i<(32-first_string); i++ ) {
        qfprintf(fptr_pat, "..");
    }

// PART #4
    // put together the crc data
    int pos = 32;
    while ( (pos < len) && (!v_bytes[pos]) && (pos < 255+32) ) {
        crc_data[pos-32] = get_byte(start_ea+pos);
        pos++;
    }

// PART #5
    // alen is length of the crc data
    alen = pos - 32;
    crc = local_crc16(crc_data, alen);
    qfprintf(fptr_pat, " %02X %04X %04X", alen, crc, len);


// PART #6:    Write Public Names
    // write the publics
    for ( std::vector<ea_t>::iterator p = qpublics.begin(); p != qpublics.end(); p++ ) {
        // Get name of public
        name = get_true_name(BADADDR, *p, buf, MAXNAMELEN);
        xoff = (*p-start_ea);

        // make sure we have a name
        if (name == NULL) {
            g_badp_ctr++;                   // Inc Bad Publics

        // Is it a user-specified name? (valid name & !dummy prefix)
        } else if ( is_uname(name) ) {
            // check for negative offset and adjust output
            if ( xoff >= 0) {
                qfprintf(fptr_pat, " :%04X %s", xoff, name);
            } else {
                xoff *= -1;
                qfprintf(fptr_pat, " :-%04X %s", xoff, name);
            }

        // grab autogen "sub_" names
        } else if ( (strstr(name, "sub_")) && (opt_ptr->chkbx & CHKBX_DO_SUBS) ) {
            // Use our own prefix so there isn't a reserved prefix problem
            qstrncpy(xname, "FAKE_", MAXNAMELEN);
            qstrncat(xname, name, MAXNAMELEN-7);
            if (xname != NULL) {
                // check for negative offset and adjust output
                if ( xoff >= 0) {
                    qfprintf(fptr_pat, " :%04X %s", xoff, xname);
                } else {
                    xoff *= -1;
                    qfprintf(fptr_pat, " :-%04X %s", xoff, xname);
                }
            }
        } else {
            g_badp_ctr++;                   // Inc Bad Publics
        }
    }



// PART #7     Write named referneces
    // (*r).first   holds the ea in the function where the reference is used
    // (*r).second  holds the ea of the reference itself

    // write the references
    for ( ref_map::iterator r = refs.begin(); r != refs.end(); r++ ) {
        // Get name of reference
        name = get_true_name(BADADDR, (*r).second, buf, MAXNAMELEN+1);
        xoff = ((*r).first-start_ea);

        mflags = getFlags((*r).second);

        // make sure we have a name
        if (name == NULL) {
            g_badr_ctr++;                       // Inc bad refs counter

        // Is it a user-specified name?
        } else  if (has_user_name(mflags)) {
            // check for negative offset and adjust output
            if ( xoff >= 0) {
                qfprintf(fptr_pat, " ^%04X %s", xoff, name);
            } else {
                xoff *= -1;
                qfprintf(fptr_pat, " ^-%04X %s", xoff, name);
            }

        // grab autogen "sub_" names
        } else if ( (strstr(name, "sub_")) && (opt_ptr->chkbx & CHKBX_DO_SUBS) ) {
            // Use our own prefix so there isn't a reserved prefix problem
            qstrncpy(xname, "FAKE_", MAXNAMELEN);
            qstrncat(xname, name, MAXNAMELEN-7);
            if (xname != NULL) {
                // check for negative offset and adjust output
                if ( xoff >= 0) {
                    qfprintf(fptr_pat, " ^%04X %s", xoff, xname);
                } else {
                    xoff *= -1;
                    qfprintf(fptr_pat, " ^-%04X %s", xoff, xname);
                }
            }
        } else {
            g_badr_ctr++;                       // Inc bad refs counter
        }
    }


// PART #8
    // and finally write out the last string with the rest of the function
    qfprintf(fptr_pat, " ");
    for ( i = pos; i<len; i++ ) {
        if ( v_bytes[i] ) {
            qfprintf(fptr_pat, "..");
        } else {
            qfprintf(fptr_pat, "%02X", get_byte(start_ea+i));
        }
    }
    g_pats_ctr++;
    qfprintf(fptr_pat, "\n");
    qflush(fptr_pat);
}


// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// FUNCTION: opt_diaolg
//
// Dialog for gettig user desired options
//
PATOPTION* opt_diaolg(PATOPTION* opt_ptr) {

    // Build the format string constant used to create the dialog
    const char format[] =
    "STARTITEM 0\n"                                                 // TabStop
    "HELP\n"                                                        // Help
    "**********************************************************************\n"
    "                                                                      \n"
    "                              IDB_2_PAT                               \n"
    "                                                                      \n"
    "For the most part, this plugin is an exercise in futility. There are  \n"
    "very few valid reasons why anyone should ever want to build signatures\n"
    "of the functions in an existing disassemblly. There are better        \n"
    "reasons, methods and tools for creating signatures for use with IDA.  \n"
    "Most importantly, the right way to create signatures is from object   \n"
    "files, oject libraries or dynamically linked libraries, so please     \n"
    "realize this plugin is nothing more than a kludge since we are asking \n"
    "FLAIR to do something it was not designed to do.                      \n"
    "                                                                      \n"
    "**********************************************************************\n"
    "Option: Create patterns for Non-Auto Named Functions                  \n"
    "                                                                      \n"
    "    If you find the rare situation where you want to make patterns    \n"
    "from functions in an existing database, this option is probably your  \n"
    "best bet. It will only create patterns for functions without          \n"
    "autogenerated names and it will exclude functions marked as libraries \n"
    "(e.g. they were already found and named through other FLAIR           \n"
    "signatures). You may want to remove named functions like _main and    \n"
    "WinMain from the resulting pattern file, since these will already     \n"
    "exist in the disassembly where it's applied.                          \n"
    "                                                                      \n"
    "**********************************************************************\n"
    "Option: Create Patterns for Library Functions Only                    \n"
    "                                                                      \n"
    "    I did include the ability to build patterns for functions IDA has \n"
    "already marked as libraries. This is forpeople doing source code      \n"
    "recovery/recreation since the pattern file can be further parsed to   \n"
    "figure out which header files are needed. There are probably better   \n"
    "ways togo about this as well but until I have time to write specific a\n"
    "plugin for figureing out which headers are included, this can give you\n"
    "a step in the right direction.Out side of gathering information on    \n"
    "applied library signatures, this feature is pointless since you're    \n"
    "building patternss for function that were previously found with other \n"
    "signatures you already have.                                          \n"
    "                                                                      \n"
    "**********************************************************************\n"
    "Option: Create Patterns for Public Functions Only                     \n"
    "                                                                      \n"
    "    This could be useful when dealing with a situation where functions\n" 
    "were once stored in a DLL and are now statically linked in an         \n"
    "executable. It's still may a better bet to build a signature from the \n"
    "DLL and then apply it to the statically linked executable.            \n"
    "                                                                      \n"
    "**********************************************************************\n"
    "Option: Create Patterns For Everything                                \n"
    "                                                                      \n"
    "    You generally do NOT want to build patterns for every function in \n"
    "the disassembly. The only place where I can see a legitimate use for  \n"
    "creating signatures of every functionin the database is if your goal  \n"
    "is to see how similar two executables are. Instead of using a hex     \n"
    "editor and doing aresyncronizing binary compare between the two       \n"
    "executables,you could use IDA signatures to get a different/better    \n"
    "wayto visualize the similarities.                                     \n"
    "                                                                      \n"
    "    There are a lot of problems with trying to do this. The first and \n"
    "most obvious problem is reserved name prefixes (e.g. sub_) on         \n"
    "autogenerated function names. Another cascading problem is of course  \n"
    "references to these names withing other functions and whether or not  \n"
    "to keep these references in the patterns in order to cut down the     \n"
    "numberof collisions. There are plenty of other problems with this     \n"
    "approach that I won't mention but there are quite a few ofthem.       \n"
    "                                                                      \n"
    "    I've hacked together a simple work-around. When the user has      \n"
    "selected everything mode, the pulgin will prepend the autogenerated   \n"
    "function names with FAKE_ and references to these sub routines are    \n"
    "kept to reduce collisions. This should (in theory) work, since every  \n"
    "reference will also have it's own public pattern in the resulting     \n"
    "file. In other words, the named references will resolve to another    \n"
    "(public) function pattern in the file. The problem with this approach \n"
    "is of course having erroneous address numbers in names of functions   \n"
    "where the signature is applied (e.g. the nameFAKE_sub_DEADBEEF could  \n"
    "be applied to any anddress where a matching function is found). My    \n"
    "guess why this will work is because a module in a library may have a  \n"
    "by name reference to another object in the library. The pattern file  \n"
    "of a library would keep the references, since the names are defined   \n"
    "in other pattern lines of the file. Of course I could be wrong but    \n"
    "it's worth a shot. If need be comment out the 'sub_' tests in         \n"
    "part #7 (references) of make_pattern() to get rid of the refs. So far \n"
    "it has worked well for avoiding collisions, On my test file with      \n"
    "1090 functions there were no collisions between 'FAKE_sub_' functions.\n"
    "                                                                      \n"
    "**********************************************************************\n"
    "Option: Create Pattern For User Selected Function                     \n"
    "                                                                      \n"
    "    This allows the user to select a function from the list  and      \n"
    "create a pattern for it. It does not work on functions with auto      \n"
    "generated names but probably could with a bit more work.              \n"
    "                                                                      \n"
    "**********************************************************************\n"
    "                                                                      \n"
    "  Please see the readme.txt for more details like limitations         \n"
    "                                                                      \n"
    "ENDHELP\n"
    "Choose Option\n"                                               // Title
    "Please choose the method for selecting functions.\n\n"         // MsgText


     //  Radio Button 0x0000
    "<#Create patterns for all functions with user created names.\n"// hint0
    "This excludes all library functions and auto-generated names.#"// hint0
    "Non-Auto Named Functions:R>\n"                                 // text0

     //  Radio Button 0x0001
    "<#Create patterns for functions maked as libraries.\n"         // hint1
    "This excludes all auto-generated names.#"                      // hint1
    "Library Functions Only:R>\n"                                   // text1

     //  Radio Button 0x0002
    "<#Create patterns for functions marked as public.\n"           // hint2
    "This excludes all auto-generated names.#"                      // hint2
    "Public Functions Only:R>\n"                                    // text2

     //  Radio Button 0x0003
    "<#CAUTION -This will make a real mess of names in any\n"       // hint3
    "disassembly where the resulting signature is applied.#"        // hint3
    "Create Patterns For Everything:R>\n"                           // text3

     //  Radio Button 0x0004
    "<#You get prompted to choose a function from the list.#"       // hint4
    "User Selected Function:R>>\n\n"                                // text4

    // Check Boxes  -Not Implemented Yet...
//    "<# Hint #Checkbox 0x0001:C>\n"                                  // 0x0001
//    "<# Hint #CheckBox 0x0002:C>>\n\n"                               // 0x0002
//    "<# Hint #CheckBox 0x0004:C>>\n\n"                               // 0x0002
    ; // End Dialog Format String

    // Starting value is masked to set which radio button is checked by default.
    opt_ptr->radio = RADIO_NON_FUNC;                    // Set Default Radio

    // Starting value is masked to set which boxes are checked by default.
    opt_ptr->chkbx = CHKBX_DO_NADA;                     // Set Default ChkBox

    // Create the option dialog.
    int ok = AskUsingForm_c(format, &(opt_ptr->radio));

    if (!ok){
        opt_ptr->radio = RADIO_IS_ERROR;                        // Error Occured
    }

    if (opt_ptr->radio == RADIO_ALL_FUNC) {                     // Set up hoser
        opt_ptr->chkbx = (opt_ptr->chkbx) + CHKBX_DO_LIBS;
        opt_ptr->chkbx = (opt_ptr->chkbx) + CHKBX_DO_SUBS;
    }

// debug msgs -they will show you the size mismatch problems of using ints
// (enums and #defines) with functions like AskUsingForm_c(). ChkBox and radio
// vars/defs have been set to "const short int" in the header file.
//    short int   xshrtint = 0;
//    int         xrealint = 0;
//    long int    xlongint = 0;
//    msg("shortint == %i\narealint == %i\n",sizeof(xshrtint),sizeof(xrealint));
//    msg("alongint == %i\n", sizeof(xlongint));
//    msg("#define  == %i\n", sizeof(MIN_SIG_LENGTH));
//    msg("opt_ptr->radio == %i\nopt_ptr->chkbx == %i\n",
//        opt_ptr->radio, opt_ptr->chkbx);
//
    return opt_ptr;
}

// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// FUNCTION: get_pat_file
//
// Set pattern file name and open file for writing
//
FILE* get_pat_file()
{
    char* filename;
    FILE* fptr_pat;
    filename = askfile_c(1, "*.pat", "Enter the name of the pattern file:");
    fptr_pat = qfopen(filename, "w");
    if ( !fptr_pat ) {
        warning("Could not open %s for writing!\n", filename);
    } else {
        msg("Using: %s\n", filename);
    }
    return fptr_pat;
}



// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
// FUNCTION: run
//
// The main plugin
//
void run(int arg)
{
    FILE* fptr_pat;                     // Pattern file
    func_t* funcstru;                   // Function structure
    int i = 0;                          // Counters
    int funcqty = 0;                    // Total Number of Functions
    char buf[MAXNAMELEN+1];             // Function Name Buffer
    char *name;                         // Function Name

    // Plugin start message
    msg(" Start IDB_2_PAT \n");

    // reset global counters. -necessary because of how plugins are handled
    g_skip_ctr = 0;                       // skiped function counter
    g_shrt_ctr = 0;                       // too short function counter
    g_libs_ctr = 0;                       // lib function counter
    g_pubs_ctr = 0;                       // pub function counter
    g_badf_ctr = 0;                       // bad function number counter
    g_badn_ctr = 0;                       // bad function name counter
    g_badp_ctr = 0;                       // Bad Public Name Counter in patern
    g_badr_ctr = 0;                       // Bad Reference Name Counter in pat
    g_pats_ctr = 0;                       // Number of Patterns Created


    // get file for pattern (*.PAT) and test result
    fptr_pat = get_pat_file();
    if ( !fptr_pat ) {
        msg("ERROR: in run() opening *.PAT file\n");
        return;
    }

    // get user desired options and test result
    opt_ptr = opt_diaolg(opt_ptr);
    if (opt_ptr->radio == -1) {
        msg("ERROR in opt_diaolg() or user chose cancel.\n");
        return;
    }

    // Get number of function and test result.
    funcqty = get_func_qty();
    if ( funcqty == 0) {
        msg("ERROR get_func_qt() == 0  No Functions defined!");
        return;
    }


    // Handle the choice of user selected function
    //   CASE 5 == RADIO_USR_FUNC  (build pattern for user selected function)
    //
    if (opt_ptr->radio == RADIO_USR_FUNC) {
        // Do the "Choose Function" dialog
        funcstru = choose_func("Choose Function",-1);
        // test to make sure we got a funct_t structure
        if ( !funcstru ) {
            msg("WARNING: funcstru = choose_func() FAILED\n");
            g_skip_ctr++;                     // Inc skiped function counter
            g_badf_ctr++;                     // Inc the bad function # counter
        // test for min function length
        } else if ( (funcstru->endEA - funcstru->startEA) < MIN_SIG_LENGTH ) {
            msg("WARNING: Min function length FAILED on %08x\n", funcstru->startEA);
            g_skip_ctr++;                     // Inc skiped function counter
            g_shrt_ctr++;                     // Inc function too Short counter

        // test for function has a name
        } else if ((name = get_name(BADADDR, funcstru->startEA, buf,
        MAXNAMELEN+1)) == NULL) {
            msg("WARNING: name = get_name() FAILED on %08x\n", funcstru->startEA);
            g_skip_ctr++;                     // Inc skiped function counter
            g_badn_ctr++;                     // inc the bad name counter

        // we're ready to roll...
        } else {
            // Make the pattern
            make_pattern( funcstru, fptr_pat, opt_ptr );
        }

    // Handle the other choices
    //   CASE 0 == RADIO_NON_FUNC  (build patterns for non auto-named functions)
    //   CASE 1 == RADIO_LIB_FUNC  (build patterns for library functions)
    //   CASE 2 == RADIO_PUB_FUNC  (build patterns for public functions)
    //   CASE 3 == RADIO_ALL_FUNC  (build patterns for everything)
    //
    } else {
        for ( i = 0; i < funcqty; i++ ) {
            funcstru = getn_func(i);              // get current function

            // test to make sure we have a function structure
            if ( !funcstru ) {
                msg("WARNING: funcstru = getnfunc(i) FAILED on func #%i\n", i);
                g_skip_ctr++;                     // Inc skiped function counter
                g_badf_ctr++;                     // Inc bad function counter

            // test to make sure the function is long enough to create pattern
            } else if ( (funcstru->endEA - funcstru->startEA) < MIN_SIG_LENGTH ) {
                msg("WARNING: Min func length FAILED on # %i at %08x\n", i, funcstru->startEA);
                g_skip_ctr++;                     // Inc skiped function counter
                g_shrt_ctr++;                     // Inc short function counter

            // make sure function has a name
            } else if ((name = get_name(BADADDR, funcstru->startEA, buf,
            MAXNAMELEN+1)) == NULL) {
                msg("WARNING: name = get_name() FAILED on # %i at %08x\n", i, funcstru->startEA);
                g_skip_ctr++;                     // Inc skiped function counter
                g_badn_ctr++;                     // inc the bad name counter

            // We're ready to roll...
            } else {

                if ((funcstru->flags & FUNC_LIB)) {
                    g_libs_ctr++;                 // Inc the libs counter
                }

                if ( is_public_name(funcstru->startEA) ) {
                    g_pubs_ctr++;                 // Inc the pubs counter
                }

                switch (opt_ptr->radio) {

                    // CASE 0 == RADIO_NON_FUNC  (pats non auto-named functions)
                    case RADIO_NON_FUNC:
                        if ( is_uname(name) && !(funcstru->flags & FUNC_LIB) ) {
                            make_pattern( funcstru, fptr_pat, opt_ptr );
                        } else {
                            g_skip_ctr++;         // Inc skiped function counter
                        }
                        break;

                    // CASE 1 == RADIO_LIB_FUNC  (pattern for library functions)
                    case RADIO_LIB_FUNC:
                        if ((funcstru->flags & FUNC_LIB)) {
                            make_pattern( funcstru, fptr_pat, opt_ptr );
                        } else {
                            g_skip_ctr++;         // Inc skiped function counter
                        }
                        break;

                    // CASE 2 == RADIO_PUB_FUNC  (patterns for public functions)
                    case RADIO_PUB_FUNC:
                        if ( is_public_name(funcstru->startEA) ) {
                            make_pattern( funcstru, fptr_pat, opt_ptr );
                        } else {
                            g_skip_ctr++;         // Inc skiped function counter
                        }
                        break;

                    // CASE 3 == RADIO_ALL_FUNC  (patterns for everything)
                    case RADIO_ALL_FUNC:
                        opt_ptr->chkbx = CHKBX_DO_SUBS;
                        make_pattern( funcstru, fptr_pat, opt_ptr );
                        break;

                    // default error
                    default:
                        msg("ERROR: in run() at switch: %s", __LINE__);
                        return;
                } // End switch
            } // End else
        } // End for
    } // End else

    // Check for file ptr, write pattern EOF marker and close file
    if (fptr_pat) {
        qfprintf(fptr_pat, "---\n");         // add end of *.PAT file marker
        qfclose(fptr_pat);                   // close file handle
    }


// print out the stats
    msg("\nTotal # of Funtions     funcqty == %i\n", funcqty);
    msg("Total Loop Runs                i  == %i\n", i);
    msg("# of Pub Function      g_pubs_ctr == %i\n", g_pubs_ctr);
    msg("# of Lib Function      g_libs_ctr == %i\n", g_libs_ctr);
    msg("# of Skipped           g_skip_ctr == %i\n", g_skip_ctr);
    msg("# of Short Functions   g_shrt_ctr == %i\n", g_shrt_ctr);
    msg("# of Bad Func Names    g_badn_ctr == %i\n", g_badn_ctr);
    msg("# of Bad Func #'s      g_badf_ctr == %i\n", g_badf_ctr);
    msg("# of Bad Pub Names     g_badp_ctr == %i\n", g_badp_ctr);
    msg("# of Bad Ref Names     g_badp_ctr == %i\n", g_badr_ctr);
    msg("Total Funcion Patterns Created    == %i\n", g_pats_ctr);

// Plugin Finished message
    msg("\nIDB_2_PAT Finished!\n");
}



// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
//
// This callback is called for UI notification events
//
static int sample_callback(void * /*user_data*/, int event_id, va_list /*va*/)
{
  if ( event_id != ui_msg )     // avoid recursion
    if ( event_id != ui_setstate
      && event_id != ui_showauto
      && event_id != ui_refreshmarked ) // ignore uninteresting events
        msg("ui_callback %d\n", event_id);
  return 0;                     // 0 means "process the event"
                                // otherwise the event would be ignored
}

// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
//
//      Initialize.
//
//      IDA will call this function only once.
//      If this function returns PLGUIN_SKIP, IDA will never load it again.
//      If this function returns PLUGIN_OK, IDA will unload the plugin but
//      remember that the plugin agreed to work with the database.
//      The plugin will be loaded again if the user invokes it by
//      pressing the hotkey or selecting it from the menu.
//      After the second load the plugin will stay on memory.
//      If this function returns PLUGIN_KEEP, IDA will keep the plugin
//      in the memory. In this case the initialization function can hook
//      into the processor module and user interface notification points.
//      See the hook_to_notification_point() function.
//
//      In this example we check the input file format and make the decision.
//      You may or may not check any other conditions to decide what you do:
//      whether you agree to work with the database or not.
//
int init(void)
{
  if ( inf.filetype == f_ELF ) return PLUGIN_SKIP;

// Please uncomment the following line to see how the notification works
//  hook_to_notification_point(HT_UI, sample_callback, NULL);

// Please uncomment the following line to see how the user-defined prefix works
//  set_user_defined_prefix(prefix_width, get_user_defined_prefix);

  return PLUGIN_KEEP;
}

// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
//
//      Terminate.
//      Usually this callback is empty.
//      The plugin should unhook from the notification lists if
//      hook_to_notification_point() was used.
//
//      IDA will call this function when the user asks to exit.
//      This function won't be called in the case of emergency exits.

void term(void)
{
  unhook_from_notification_point(HT_UI, sample_callback);
  set_user_defined_prefix(0, NULL);
}


// _____________________________________________________________________________
// *****************************************************************************
// -----------------------------------------------------------------------------
//
//      PLUGIN DESCRIPTION BLOCK
//
// -----------------------------------------------------------------------------

extern "C" plugin_t PLUGIN = {
  IDP_INTERFACE_VERSION,
  0,                    // plugin flags
  init,                 // initialize

  term,                 // terminate. this pointer may be NULL.

  run,                  // invoke plugin

  comment,              // long comment about the plugin
                        // it could appear in the status line
                        // or as a hint

  help,                 // multiline help about the plugin

  wanted_name,          // the preferred short name of the plugin
  wanted_hotkey         // the preferred hotkey to run the plugin
};
