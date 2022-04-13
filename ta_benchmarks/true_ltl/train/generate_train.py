#! /usr/bin/env python3

import os


class Tool:
    """ Interface for the classes that create the models and properties
        for the different model checkers """

    def __init__(self, name, base_dir):
        self.name = name

        # load model template
        template_file = os.path.join(base_dir, name,
                                     f"{name}_model.template")
        assert os.path.isfile(template_file), f"Not a file: {template_file}"

        with open(template_file, 'r') as f:
            self.model_template = f.read()

        # load property template
        template_file = os.path.join(base_dir, name,
                                     f"{name}_property.template")
        if os.path.isfile(template_file):
            with open(template_file, 'r') as f:
                self.property_template = f.read()
        else:
            print(f"No property template for {name}")
            self.property_template = None

    def generate_model(self, proc_num):
        return self._instantiate_model(self.model_template, proc_num)

    def generate_property(self, proc_num):
        if self.property_template is not None:
            return self._instantiate_property(self.property_template,
                                              proc_num)
        return None

    @property
    def model_file_extension(self):
        raise NotImplementedError

    @property
    def property_file_extension(self):
        return None

    @property
    def additional_files_extensions(self):
        return None

    def _instantiate_model(self, template, proc_num):
        raise NotImplementedError

    def _instantiate_property(self, template, proc_num):
        return None


class Atmoc(Tool):
    """ Generate model and properties for ATMOC """

    def __init__(self, base_dir):
        Tool.__init__(self, "atmoc", base_dir)

    @property
    def model_file_extension(self):
        return "tsmv"

    def _instantiate_model(self, template, proc_num):
        train_decls = "\n".join(f"  train{i} : Train(a, b);"
                                for i in range(proc_num))
        only_1_train_moves = []
        for i0 in range(proc_num):
            curr = " & ".join(f"train{i1}.evt_stutter" for i1 in range(proc_num)
                              if i1 != i0)
            curr = f"TRANS !train{i0}.evt_stutter -> ({curr});"
            only_1_train_moves.append(curr)
        only_1_train_moves = "\n".join(only_1_train_moves)

        or_train_approach = " | ".join(f"train{i}.evt_approach"
                                       for i in range(proc_num))
        or_train_exit = " | ".join(f"train{i}.evt_exit"
                                   for i in range(proc_num))
        spec = " & ".join(f"(train{i}.l = t3 -> (gate.l = g2 SU train{i}.l = t0))"
                          for i in range(proc_num))
        return template.format(proc_num_p=proc_num+1,
                               train_decls=train_decls,
                               only_1_train_moves=only_1_train_moves,
                               or_train_approach=or_train_approach,
                               or_train_exit=or_train_exit,
                               spec=spec)


class Ctav(Tool):
    """ Generate model and properties for CTAV """

    def __init__(self, base_dir):
        Tool.__init__(self, "ctav", base_dir)

    @property
    def model_file_extension(self):
        return "xml"

    @property
    def prop_file_extension(self):
        return "ltl"

    @property
    def additional_files_extensions(self):
        return ['txt']

    def _instantiate_model(self, template, proc_num):
        train_decls = "\n".join(f"  train{i} = Train({i+1});"
                                for i in range(proc_num))
        train_list = ", ".join(f"train{i}" for i in range(proc_num))
        return template.format(proc_num=proc_num,
                               train_decls=train_decls,
                               train_list=train_list)

    def _instantiate_property(self, template, proc_num):
        spec = r" /\ ".join(f"(train{i}.t3 -> (gate.g2 U train{i}.t0))"
                            for i in range(proc_num))
        return template.format(spec=spec)


class Divine(Tool):
    """ Generate model and properties for DiVinE """

    def __init__(self, base_dir):
        Tool.__init__(self, "divine", base_dir)

    @property
    def model_file_extension(self):
        return "xml"

    @property
    def prop_file_extension(self):
        return "ltl"

    def _instantiate_model(self, template, proc_num):
        comps_decl = "\n".join(f"  tr{i} = Train({i});"
                               for i in range(proc_num))
        comps_list = ", ".join(f"tr{i}" for i in range(proc_num))
        return template.format(max_pid=proc_num-1,
                               comps_decl=comps_decl,
                               comps_list=comps_list)

    def _instantiate_property(self, template, proc_num):
        defines = "\n".join(f"#define t{i}_0 (tr{i}.t0)\n"
                            f"#define t{i}_3 (tr{i}.t3)"
                            for i in range(proc_num))
        spec = " && ".join(f"(t{i}_3 -> (g2 U t{i}_0))"
                           for i in range(proc_num))
        return template.format(defines=defines, spec=spec)


class Ltsmin(Tool):
    """ Generate model and properties for LTSmin """

    def __init__(self, base_dir):
        Tool.__init__(self, "ltsmin", base_dir)

    @property
    def model_file_extension(self):
        return "xml"

    @property
    def prop_file_extension(self):
        return "q"

    def _instantiate_model(self, template, proc_num):
        comps_decl = "\n".join(f"  tr{i} = Train({i});"
                               for i in range(proc_num))
        comps_list = ", ".join(f"tr{i}" for i in range(proc_num))
        return template.format(max_pid=proc_num-1,
                               comps_decl=comps_decl,
                               comps_list=comps_list)

    def _instantiate_property(self, template, proc_num):
        spec = " && ".join(f"((tr{i}_loc == 3) -> ((gate_is_g2 == 1) U (tr{i}_loc == 0)))"
                           for i in range(proc_num))
        return template.format(spec=spec)


class NuXmv(Tool):
    """ Generate model and properties for nuXmv """

    def __init__(self, base_dir):
        Tool.__init__(self, "nuxmv", base_dir)

    @property
    def model_file_extension(self):
        return "smv"

    def _instantiate_model(self, template, proc_num):
        train_decls = "\n".join(f"  train{i} : Train(a, b);"
                                for i in range(proc_num))
        only_1_train_moves = []
        for i0 in range(proc_num):
            curr = " & ".join(f"train{i1}.evt_stutter" for i1 in range(proc_num)
                              if i1 != i0)
            curr = f"TRANS !train{i0}.evt_stutter -> ({curr});"
            only_1_train_moves.append(curr)
        only_1_train_moves = "\n".join(only_1_train_moves)

        or_train_approach = " | ".join(f"train{i}.evt_approach"
                                       for i in range(proc_num))
        or_train_exit = " | ".join(f"train{i}.evt_exit"
                                   for i in range(proc_num))

        spec = " & ".join(f"(train{i}.l = t3 -> (gate.l = g2 U train{i}.l = t0))"
                          for i in range(proc_num))
        return template.format(proc_num_p=proc_num+1,
                               train_decls=train_decls,
                               only_1_train_moves=only_1_train_moves,
                               or_train_approach=or_train_approach,
                               or_train_exit=or_train_exit,
                               spec=spec)


class Uppaal(Tool):
    """ Generate model and properties for Uppaal """

    def __init__(self, base_dir):
        Tool.__init__(self, "uppaal", base_dir)

    @property
    def model_file_extension(self):
        return "xml"

    @property
    def prop_file_extension(self):
        return "q"

    def _instantiate_model(self, template, proc_num):
        comps_decl = "\n".join(f"t{i} = Train({i});"
                               for i in range(proc_num))
        comps_list = ", ".join(f"t{i}" for i in range(proc_num))
        return template.format(max_pid=proc_num-1,
                               comps_decl=comps_decl,
                               comps_list=comps_list)

    def _instantiate_property(self, template, proc_num):
        spec = " and ".join(f"(t{i}.train3 imply (gate.gate2 U t{i}.train0))"
                            for i in range(proc_num))
        return template.format(spec=spec)


def clean(base_dir, tools):
    to_remove = []
    for tool in tools:
        inst_file = os.path.join(base_dir, f"{tool.name}_instances.txt")
        if os.path.isfile(inst_file):
            os.remove(inst_file)
        curr_dir = os.path.join(base_dir, tool.name)
        if os.path.isdir(curr_dir):
            to_remove.append((curr_dir, "." + tool.model_file_extension))
            if hasattr(tool, "prop_file_extension") and \
               tool.prop_file_extension is not None:
                to_remove.append((curr_dir, "." + tool.prop_file_extension))
            if hasattr(tool, "additional_files_extensions") and \
               tool.additional_files_extensions is not None:
                for ext in tool.additional_files_extensions:
                    to_remove.append((curr_dir, "." + ext))

    for curr_path, ending in to_remove:
        for filename in os.listdir(curr_path):
            filename = os.path.join(curr_path, filename)
            if filename.endswith(ending) and os.path.isfile(filename):
                os.remove(filename)


def main(num_models, bench_label):
    base_dir = os.path.dirname(os.path.realpath(__file__))
    base_dir = os.path.abspath(base_dir)
    tools = [# Atmoc(base_dir),  # can only falsify.
             Ctav(base_dir),
             Divine(base_dir),
             Ltsmin(base_dir),
             NuXmv(base_dir),
             # Uppaal(base_dir)  # spec not in language.
    ]

    clean(base_dir, tools)

    if num_models <= 0:
        return

    for tool in tools:
        with open(os.path.join(base_dir, f"{tool.name}_instances.txt"),
                  'w') as bench_lst:
            for proc_num in range(2, num_models + 2):
                bench_file = os.path.join(f"./{tool.name}", f"{bench_label}_{proc_num:04d}")
                bench_lst.write(f"{bench_file}.{tool.model_file_extension}\n")
                model = tool.generate_model(proc_num)
                prop = tool.generate_property(proc_num)
                name = os.path.join(base_dir, f"{tool.name}")
                name = os.path.abspath(name)
                # os.makedirs(name, exist_ok=True)
                name = os.path.join(name, f"{bench_label}_{proc_num:04d}")
                model_out = f"{name}.{tool.model_file_extension}"
                with open(model_out, 'w') as f:
                    f.write(model)
                if prop is not None:
                    prop_out = f"{name}.{tool.prop_file_extension}"
                    with open(prop_out, 'w') as f:
                        f.write(prop)


def config_args():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("num", type=int,
                   help="number of models to generate; 0 for delete.")
    return p


if __name__ == "__main__":
    main(config_args().parse_args().num, "tltl_train_gate")
