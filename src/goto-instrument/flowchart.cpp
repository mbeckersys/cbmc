/*******************************************************************\

Module: Dump flowchart

Author: Martin Becker, becker@rcs.ei.tum.de

\*******************************************************************/

#include <iostream>
#include <fstream>
#include <sstream>

#include "flowchart.h"


class flowchartt {

    typedef std::set<goto_programt::const_targett> t;

public:
    flowchartt(const goto_functionst &_goto_functions, const namespacet &_ns, bool _make_bb) : ns(_ns), subgraphscount(0), make_bb(_make_bb) {
        // take a copy of the program, since we modify it
        goto_functions.copy_from(_goto_functions);
    }

    void output(std::ostream &out);

protected:
    const namespacet&ns; ///< not a copy of input
    goto_functionst goto_functions; ///< not a copy of input

    unsigned subgraphscount;
    bool make_bb; ///< if true, then collapse flow chart, such that it shows basic blocks (at source level)

    std::list<exprt> function_calls;
    std::list<exprt> clusters;

    void write_dot_subgraph(std::ostream &, const std::string &, const goto_programt &);

    void do_dot_function_calls(std::ostream &);

    std::string &escape(std::string &str);

    void write_edge(std::ostream &, const goto_programt::instructiont &, const goto_programt::instructiont &, const std::string &);

    /**
     * @brief find successor instructions of an instruction
     */
    void find_next(const goto_programt::instructionst &, const goto_programt::const_targett &, std::set<goto_programt::const_targett> &, std::set<goto_programt::const_targett> &);

    /**
     * @brief show targets of given instruction
     */
    void dump_next(const goto_programt::instructionst &instructions, const goto_programt::const_targett &it);

    /**
     * @brief bring goto program into the correct form to be a flow chart
     */
    void _flowchart_prepare(void) /* non-const */;
    void _flowchart_prepare_subprogram(goto_programt &goto_program) /* non-const */;
};

void flowchartt::_flowchart_prepare_subprogram(goto_programt &goto_program) {
    goto_programt::instructionst instructions = goto_program.instructions;
    if(instructions.size()==0) return;

    // avoid processing instructions twice
    std::set<goto_programt::targett> seen; // instructions that we already processed
    goto_programt::targetst worklist;
    worklist.push_back(instructions.begin());

    while(!worklist.empty()) {
        goto_programt::targett ins=worklist.front();
        worklist.pop_front();

        // if we are at the end or already have processed this instruction, then skip it
        if(ins==instructions.end() || seen.find(ins)!=seen.end()) continue;

        // get successors of current ins
        std::set<goto_programt::const_targett> tres;
        std::set<goto_programt::const_targett> fres;
        find_next(instructions, ins, tres, fres);

        /*****************************
         * REMOVE unconditional GOTOs
         *****************************/
        // for TRUE guards...
        for (t::iterator it=tres.begin(); it!=tres.end(); it++) {
            if ((*it)->is_goto()) { // successor is a GOTO && it->guard.is_true()
                std::set<goto_programt::const_targett> ttar; // targets which have TRUE guards, i.e., no guards
                std::set<goto_programt::const_targett> ftar; // targets which have guards
                find_next(instructions, *it, ttar, ftar);
                std::cout << "GOTO follows as TRUE after " << ins->source_location.as_string() << ": ttar=" << ttar.size() << ", ftar=" << ftar.size() << std::endl;

                if (ftar.empty() && ttar.size() == 1) { // unconditional GOTOs should not have (false) guards
                    /**************************
                     * found one...
                     **************************/
                    // set successor of ins as being GOTO's target
                    std::cout << "BEFORE:" << std::endl;
                    dump_next(instructions, ins);

                    // we were at TRUE, i.e., we jmp -> that works.

                    goto_programt::targett goto_target = (*it)->get_target(); // target
                    goto_target->guard = (*it)->guard; // but guard is that from GOTO, not of its successor
                    ins->targets.insert(ins->targets.begin(), goto_target);
                    // FIXME: remove GOTO as target of ins
//                    (*it)->make_skip(); // remove GOTO from insn list

                    std::cout << "AFTER:" << std::endl;
                    dump_next(instructions, ins);
                    std::cout << "### removed goto" << std::endl;
                }
            }
        }
        // for other guards... (FIXME: duplicate code)
        for (t::iterator it=fres.begin(); it!=fres.end(); it++) {
            if ((*it)->is_goto()) { // successor is a GOTO
                std::set<goto_programt::const_targett> ttar; // targets which have TRUE guards, i.e., no guards
                std::set<goto_programt::const_targett> ftar; // targets which have guards
                find_next(instructions, *it, ttar, ftar);
                std::cout << "GOTO follows as FALSE after " << ins->source_location.as_string() << ": ttar=" << ttar.size() << ", ftar=" << ftar.size() << std::endl;

                if (ftar.empty() && ttar.size() == 1) { // unconditional GOTOs should not have guards
                    /**************************
                     * found one...
                     **************************/
                    // set successor of ins as being ttar
                    std::cout << "BEFORE:" << std::endl;
                    dump_next(instructions, ins);

                    // ERROR/POBLEM: it is not possible to jump to GOTO's target here, since we are in cond=FALSE successor of insn, and jmp is not possible. In GOTO programs, it is expected that the FALSE body comes immediately after the branch. Workaround: GOTO -> SKIP

                    goto_programt::targett goto_target = (*it)->get_target(); // target
                    goto_target->guard = (*it)->guard; // but guard is that from GOTO, not of its successor
                    ins->targets.insert(ins->targets.begin(), goto_target);
                    // FIXME: remove GOTO as target of ins
                    // (*it)->make_skip(); // remove GOTO from insn list

                    std::cout << "AFTER:" << std::endl;
                    dump_next(instructions, ins);
                    std::cout << "### removed goto" << std::endl;
                }
            }
        }


#if 0
        /**************************
         * BUILD BASIC BLOCKS
         **************************/
        if(ins->is_end_function()) {
        } else if(ins->is_function_call()) {
        } else if(ins->is_assign() || ins->is_decl() || ins->is_return() || ins->is_other()) {
        }
#endif

        // mark current instruction as "processed", and put the instruction that follows
        // (not necessarily goto target) into work list
        seen.insert(ins);
        goto_programt::targetst temp;
        goto_program.get_successors(ins, temp);
        worklist.insert(worklist.end(), temp.begin(), temp.end());
    }

}

void flowchartt::_flowchart_prepare(void) {
    // go over all subprograms...
    for(goto_functionst::function_mapt::iterator it=goto_functions.function_map.begin();
        it!=goto_functions.function_map.end();
        it++)
    {
        if(it->second.body_available()) {
            _flowchart_prepare_subprogram(it->second.body); // do it
        }
    }
}

/*******************************************************************\
Function: flowchartt::write_dot_subgraph
  Inputs: output stream, name and goto program
 Outputs: true on error, false otherwise
 Purpose: writes the dot graph that corresponds to the goto program
          to the output stream.
\*******************************************************************/

void flowchartt::write_dot_subgraph
(std::ostream &out, const std::string &name, const goto_programt &goto_program)
{
    clusters.push_back(exprt("cluster"));
    clusters.back().set("name", name);
    clusters.back().set("nr", subgraphscount);

    out << "subgraph \"cluster_" << name << "\" {" << std::endl;
    out << "label=\"" << name << "\";" << std::endl;

    const goto_programt::instructionst& instructions = goto_program.instructions;

    if(instructions.size()==0) {
        out << "Node_" << subgraphscount << "_0 " <<
            "[shape=Mrecord,fontsize=22,label=\"?\"];" << std::endl;
    } else {
        std::set<goto_programt::const_targett> seen;
        goto_programt::const_targetst worklist;
        worklist.push_back(instructions.begin());

        while(!worklist.empty()) {
            goto_programt::const_targett it=worklist.front();
            worklist.pop_front();

            // if we are at the end or already have processed this instruction, then skip it
            if(it==instructions.end() || seen.find(it)!=seen.end()) continue;

            //if (it->is_goto() && it->guard.is_true()) continue; // prepare() has processed them

            std::stringstream tmp("");
            if(it->is_goto()) {
                if(it->guard.is_true()) {
                    tmp.str("Goto"); // TODO: do not dump; it is actually an edge
                } else {
                    /**************************
                     * IF-CHECK
                     **************************/
                    std::string t = from_expr(ns, "", it->guard);
                    while (t[ t.size()-1 ]=='\n')
                        t = t.substr(0,t.size()-1);
                    tmp << escape(t) << "?";
                }
            } else if(it->is_assume()) {
                std::string t = from_expr(ns, "", it->guard);
                while (t[ t.size()-1 ]=='\n')
                    t = t.substr(0,t.size()-1);
                tmp << "Assume\\n(" << escape(t) << ")";
            } else if(it->is_assert()) {
                std::string t = from_expr(ns, "", it->guard);
                while (t[ t.size()-1 ]=='\n')
                    t = t.substr(0,t.size()-1);
                tmp << "Assert\\n(" << escape(t) << ")";
            }
            else if(it->is_skip())
                tmp.str("Skip");
            else if(it->is_end_function())
                tmp.str("End of Function");
            else if(it->is_location())
                tmp.str("Location");
            else if(it->is_dead())
                tmp.str("Dead");
            else if(it->is_atomic_begin())
                tmp.str("Atomic Begin");
            else if(it->is_atomic_end())
                tmp.str("Atomic End");
            else if(it->is_function_call()) {
                std::string t = from_expr(ns, "", it->code);
                while (t[ t.size()-1 ]=='\n') {
                    t = t.substr(0,t.size()-1);
                }
                tmp.str(escape(t));

                exprt fc;
                std::stringstream ss;
                ss << "Node_" << subgraphscount << "_" << it->location_number;
                fc.operands().push_back(exprt(ss.str()));
                fc.operands().push_back(it->code.op1());
                function_calls.push_back(fc);
            } else if(it->is_assign() || it->is_decl() || it->is_return() || it->is_other()) {
                std::string t = from_expr(ns, "", it->code);
                while (t[ t.size()-1 ]=='\n')
                    t = t.substr(0,t.size()-1);
                tmp.str(escape(t));
            }
            else if(it->is_start_thread())
                tmp.str("Start of Thread");
            else if(it->is_end_thread())
                tmp.str("End of Thread");
            else if(it->is_throw())
                tmp.str("THROW");
            else if(it->is_catch())
                tmp.str("CATCH");
            else
                tmp.str("UNKNOWN");


            /**************************
             * GET SUCCESSOR INSNS
             **************************/
            std::set<goto_programt::const_targett> tres;
            std::set<goto_programt::const_targett> fres;
            find_next(instructions, it, tres, fres);
            unsigned int n_out = tres.size() + fres.size();

            /**************************
             * DRAW NODE
             **************************/
//            if (!(it->is_goto() && n_out==1)) {
                out << "Node_" << subgraphscount << "_" << it->location_number;
                out << " [shape=";
                if(it->is_goto() && !it->guard.is_true() && !it->guard.is_false()) {
                    out << "diamond";
                } else {
                    out <<"Mrecord";
                }
                out << ",fontsize=22,label=\"";
                out << tmp.str();
                out << "\\n" << it->source_location.as_string();
                out << "\"];" << std::endl;
                //          }

            /**************************
             * DRAW EDGES TO SUCCESSORS
             **************************/
            if (!it->is_goto()) {
                /*******************************************
                 * CURRENT INSN: simple, only one successor
                 *******************************************/

                for (t::iterator frit=fres.begin(); frit!=fres.end(); frit++) {
                    write_edge(out, *it, **frit, "");
                }
                for (t::iterator trit=tres.begin(); trit!=tres.end(); trit++) {
                    //write_edge(out, *it, **trit, "UNCOND, t");
                    assert(false); // should not happen, since non-goto instructions have no guards
                }
                // FIXME: if successor is a GOTO, then draw edge to GOTO's successor
            } else {
                /**************************
                 * CURRENT INSN: a GOTO
                 **************************/
                if (n_out > 1){ //(it->guard.is_true() || it->guard.is_false()))) {
                    /**************************
                     * CURRENT INSN: a branch
                     **************************/
                    // draw edges to its successors
                    for (t::iterator trit=tres.begin();
                         trit!=tres.end();
                         trit++) {
                        write_edge(out, *it, **trit, "branch:true");
                    }
                    for (t::iterator frit=fres.begin();
                         frit!=fres.end();
                         frit++) {
                        write_edge(out, *it, **frit, "branch:false");
                    }

                    // FIXME: of successor is a GOTO, then draw edge to GOTO's successor
                } else {
                    /*************************************
                     * CURRENT INSN = UNCONDITIONAL GOTO
                     *************************************/
                    // do not draw, but draw edges to GOTO's target. will never happen after _prepare() was called.
                    // GOTOs that are no branches have only one outgoing edge that is in tres
                    for (t::iterator frit=fres.begin(); frit!=fres.end(); frit++) {
                        //write_edge(out, *it, **frit, "GOTO-UNCOND, f");
                        assert(false);
                    }
                    for (t::iterator trit=tres.begin(); trit!=tres.end(); trit++) {
                        assert(it->guard.is_true());
                        write_edge(out, *it, **trit, "GOTO-UNCOND, t");
                        //assert(false); // should not happen, since non-goto instructions have no guards
                    }

                }

            }

            // mar current
            seen.insert(it);
            goto_programt::const_targetst temp;
            goto_program.get_successors(it, temp);
            worklist.insert(worklist.end(), temp.begin(), temp.end());
        }
    }

    out << "}" << std::endl;
    subgraphscount++;
}

/*******************************************************************\
Function: flowchartt::do_dot_function_calls
  Inputs:
 Outputs:
 Purpose: ???

\*******************************************************************/
void flowchartt::do_dot_function_calls(std::ostream &out) {
    for(std::list<exprt>::const_iterator it=function_calls.begin();
        it!=function_calls.end();
        it++) {
        std::list<exprt>::const_iterator cit=clusters.begin();
        for(;cit!=clusters.end();cit++) {
            if(cit->get("name")==it->op1().get(ID_identifier)) {
                break;
            }
        }

        if(cit!=clusters.end()) {
            out << it->op0().id() <<
                " -> " "Node_" << cit->get("nr") << "_0" <<
                " [lhead=\"cluster_" << it->op1().get(ID_identifier) << "\"," <<
                "color=blue];" << std::endl;
        } else {
            out << "subgraph \"cluster_" << it->op1().get(ID_identifier) <<
                "\" {" << std::endl;
            out << "rank=sink;"<<std::endl;
            out << "label=\"" << it->op1().get(ID_identifier) << "\";" << std::endl;
            out << "Node_" << subgraphscount << "_0 " <<
                "[shape=Mrecord,fontsize=22,label=\"?\"];"
                << std::endl;
            out << "}" << std::endl;
            clusters.push_back(exprt("cluster"));
            clusters.back().set("name", it->op1().get(ID_identifier));
            clusters.back().set("nr", subgraphscount);
            out << it->op0().id() <<
                " -> " "Node_" << subgraphscount << "_0" <<
                " [lhead=\"cluster_" << it->op1().get("identifier") << "\"," <<
                "color=blue];" << std::endl;
            subgraphscount++;
        }
    }
}

/*******************************************************************\
Function: flowchartt::output
  Inputs:
 Outputs:
 Purpose:
\*******************************************************************/

void flowchartt::output(std::ostream &out) {
    _flowchart_prepare();

    out << "digraph G {" << std::endl;

    std::list<exprt> clusters;

    // for all functions
    for(goto_functionst::function_mapt::const_iterator it=goto_functions.function_map.begin();
        it!=goto_functions.function_map.end();
        it++) {
        if(it->second.body_available()) {
            write_dot_subgraph(out, id2string(it->first), it->second.body);
        }
    }
    do_dot_function_calls(out);
    out << "}" << std::endl;
}

/*******************************************************************\
Function: flowchartt::escape
  Inputs: a string
 Outputs: the escaped string
 Purpose: escapes a string. beware, this might not work for all
          kinds of strings.
\*******************************************************************/
std::string &flowchartt::escape(std::string &str) {
    for(unsigned i=0; i<str.size(); i++)     {
        if(str[i]=='\n') {
            str[i] = 'n';
            str.insert(i, "\\");
        } else if(str[i]=='\"' ||
                str[i]=='|' ||
                str[i]=='\\' ||
                str[i]=='>' ||
                str[i]=='<' ||
                str[i]=='{' ||
                str[i]=='}') {
            str.insert(i, "\\");
            i++;
        }
    }
    return str;
}

void flowchartt::dump_next(    const goto_programt::instructionst &instructions,
                               const goto_programt::const_targett &it) {
    std::set<goto_programt::const_targett> tres;
    std::set<goto_programt::const_targett> fres;

    find_next(instructions, it, tres, fres);

    for (t::iterator it=tres.begin(); it!=tres.end(); it++) {
        std::cout << " guard-true: " << (*it)->source_location.as_string() << std::endl;
    }
    for (t::iterator it=fres.begin(); it!=fres.end(); it++) {
        std::cout << " guard-false: " << (*it)->source_location.as_string() << std::endl;
    }
}

/*******************************************************************\
Function: flowchartt::find_next
  Inputs: instructions, instruction iterator, true results and
          false results
 Outputs: tres (successor when guards evaluate to true) and
          fres (successor for all other cases)
          returns nothing for unconditional GOTOs
 Purpose: finds an instructions successors (for goto graphs)

 Guards: outgoing edges belong to the instruction, incoming to the precedessor.
         therefore, non-goto instructions have only guardless edges
\*******************************************************************/
void flowchartt::find_next(
    const goto_programt::instructionst &instructions,
    const goto_programt::const_targett &it,
    std::set<goto_programt::const_targett> &tres, // true results
    std::set<goto_programt::const_targett> &fres) // false results
{
    /*
     * how GOTO works:
     * if (!inverted_guard) then next = tres
     * next = fres
     */

    // true results (targets that follow, if guard becomes true; e.g., IF part of GOTO)
    if(it->is_goto() && !it->guard.is_false()) {
        goto_programt::targetst::const_iterator gtit = it->targets.begin();
        for (; gtit!=it->targets.end(); gtit++) {
            tres.insert((*gtit));
        }
    }

    // is_true() means ?? there are no conditions; i.e., there is no jmp ??
    if(it->is_goto() && it->guard.is_true()) {
        return;
    }

    // everything else has no guards, e.g., ordinary instructions, or the ELSE part of GOTO
    goto_programt::const_targett next = it; next++;
    if(next!=instructions.end()) {
        fres.insert(next);
    }
}

/*******************************************************************\
Function: flowchartt::write_edge
  Inputs: output stream, from, to and a label
 Outputs: none
 Purpose: writes an edge from the from node to the to node and with
          the given label to the output stream (dot format)
\*******************************************************************/

void flowchartt::write_edge(
    std::ostream &out,
    const goto_programt::instructiont &from,
    const goto_programt::instructiont &to,
    const std::string &label)
{
    out << "Node_" << subgraphscount << "_" << from.location_number;
    out << " -> ";
    out << "Node_" << subgraphscount << "_" << to.location_number << " ";
    if(label!="")
    {
        out << "[fontsize=20,label=\"" << label << "\"";
        if(from.is_backwards_goto() &&
           from.location_number > to.location_number)
            out << ",color=red";
        out << "]";
    }
    out << ";" << std::endl;
}

/**
 * @brief the main function which dumps flowchart
 */
void flowchart(const goto_functionst &src, const namespacet &ns,
               std::ostream &out, bool make_bbs) {
    flowchartt chart(src, ns, make_bbs);
    chart.output(out);
}

