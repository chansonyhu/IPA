import os, sys
print(os.getcwd())
filter_file = './scripts/log_filter.txt'

DUMMY_TO = 0.00
TOTALCPUTH = 300.00
def logname2progname(file): 
    # logname: sum-ori.regression.32_7a.block--drbd--drbd.ko.set@99.320.53ea433.32_7a.cil_safe.i.log
    # progname: block--drbd--drbd.ko/320.53ea433.32_7a
    # return file
    tmp = file.split('.')
    prefix = ''
    driver_dir = tmp[3] + '/'
    revision_file = ''
    for i in range(7, 10):
    # for i in range(6, 9):
        revision_file += tmp[i] + '.'
    revision_file = revision_file[:len(revision_file) - 1]

    # return prefix + driver_dir + revision_file + '\n'
    return prefix + driver_dir + revision_file # + '\n'

def mut_logname2progname(file):
    # logname: sum-mut-f_block.initial.acpi--bgrt.set.acpi--bgrt_0.c.log
    # progname: block--drbd--drbd.ko/320.53ea433.32_7a
    # progname: acpi--bgrt/acpi--bgrt_0
    # return file
    tmp = file.split('.')
    prefix = ''
    driver_dir = tmp[2] + '/'
    revision_file = ''
    for i in range(4, 5):
        revision_file += tmp[i] + '.'
    revision_file = revision_file[:len(revision_file) - 1]

    return prefix + driver_dir + revision_file

# rst_base = './' + selector + '.2019-' + time + '.logfiles/'
rst_base = sys.argv[1]
try:
    selector = rst_base.split('.')[0] + '.' + rst_base.split('.')[1]
except:
    selector = rst_base
sum_paths = []

files = sorted(os.listdir(rst_base))
bak_files = list(files)
files = list(filter(lambda x : 'unsafe' not in x and 'DS_Store' not in x, files))

# device * spec = 259
raw_initials = []
raw_initials = list(filter(lambda x:'initial' in x, files))

# 当前logfiles里有效文件（程序结束时会输出）
valid_files = []
valid_reg_files = []
pool_initial = []

tmp_filter_list = open(filter_file, 'r').readlines()

padding_list = []
try:
    for f in tmp_filter_list:
        padding_list.append((logname2progname(f[:len(f) - 1])).replace('\n',''))
except:
    padding_list = tmp_filter_list
tmp_files = []
for file in files:
    if not file.endswith('log'):
        continue
    handle = logname2progname(file)
    
    if handle  in padding_list or handle + '\n' in padding_list:
        tmp_files.append(file)
files = tmp_files
# raw_initials = list(filter(lambda x:'initial' in x, files))

is_all_revs = False
if len(sys.argv) == 2:
    # 全部revs输出
    # 第二个参数
    is_all_revs = True
    raw_initials = files

def getInitial(x):
    tmp = x.split('.')
    if 'initial' in tmp and len(tmp) == 2:
        return None
    return tmp[2] + '.' + tmp[3]

initials = list(map(getInitial, raw_initials))
if len(sys.argv) == 2:
    # 第二个参数
    initials = raw_initials
# 构造log字典
groups = {}
for initial in initials:
    groups[initial] = []
tmp_count = 0
for file in files:
    for initial in initials:
        if initial == None:
            continue
        if initial in file:
            groups[initial].append(file)
            tmp_count += 1
            break

KEYS = [
    'abstractions',
    '1st_analysis_time',
    'solved',
    'mem (MB)',
    'refinements',
    'analysis_time (s)',
    'total_time (s)',
    'analysis_time* (s)',
    'anno hits',
    'anno_write_time',
    'anno_read_time',
    'anno size',
    'anno_reuse_time',
    'cfadiff_time',
    'impact_analysis_time',
    'RR'
    # 'solved reg'
]

def extract_float(line):
    tmp = line.split(' ')
    return round((float)(((tmp[len(tmp) - 1]).split('s'))[0]), 2)

def extract_int(line):
    tmp = line.split(' ')
    if tmp[len(tmp) - 1] == '':
        return (int)(tmp[len(tmp) - 2])
    return (int)(tmp[len(tmp) - 1])

def extract_mem(line):
    tmp = line.split('MB')
    return extract_int(tmp[0])

def extract_file_name(line):
    tmp = line.split('.')
    if len(tmp) == 12:
        return tmp[2] + '.' + tmp[3] + '.' + tmp[6]
    return line

def write_groups_info(writer, groups_info):
    separator = ','
    isHead = False
    for key,value in groups_info.items():
        if not isHead:
            head_str = 'set' + separator
            for k in value.keys():
                head_str += k + separator
            head_str += '\n'
            isHead = True
            writer.write(head_str)
        sub_str = key + separator
        for v in value.values():
            sub_str += str(v) + separator
        sub_str += '\n'
        if '.initial.' in sub_str:
            continue
        writer.write(sub_str)
    return None

def write_groups_sum(writer, groups_sum):
    separator = ','
    isHead = False
    for key,value in (groups_sum.items()):
        if not isHead:
            head_str = 'set' + separator
            if is_all_revs:
                for k in sorted(KEYS):
                    head_str += k + separator
            else:
                for k in sorted(value.keys()):
                    head_str += k + separator
            head_str += '\n'
            isHead = True
            writer.write(head_str)
        if key == None:
            continue
        
        if is_all_revs:
            if '.initial.' in key:
                continue
            tmp = (key).split('.')
            tmp_str = tmp[2] + '.' + tmp[3] + '.' + tmp[6]
            sub_str = tmp_str + separator
            for k in sorted(KEYS):
                sub_str += str(value[k]) + separator
        else:
            sub_str = key + separator
            for k in sorted(value.keys()):
                sub_str += str(value[k]) + separator
        sub_str += '\n'
        if '.initial.' in sub_str:
            continue
        writer.write(sub_str)

def write_total_sum(writer, total_sum):
    separator = ','
    sub_str = 'Total' + separator
    for key in sorted(total_sum.keys()):
        sub_str += str(total_sum[key]) + separator
    if '.initial.' in sub_str:
        return None
    writer.write(sub_str)

def build_total_sum(groups_sum):
    total_sum = {}
    keys = groups_sum.keys()
    target_values = []
    for k in keys:
        target_values.append(groups_sum[k])
    for key in KEYS:
        total_sum[key] = 0.0
    for value in target_values:
        for KEY in KEYS:
            total_sum[KEY] += value[KEY]
            total_sum[KEY] = round(total_sum[KEY], 2)
    if (total_sum['anno hits'] + total_sum['abstractions']) == 0:
        total_sum['RR'] = 0.0
    else:
        total_sum['RR'] = round((float) (total_sum['anno hits']) / (total_sum['anno hits'] + total_sum['abstractions']), 2)
    return total_sum


def build_groups_sum(countRev, countLess, initial, groups_info):
    group_sum = {}
    initials = groups_info.keys()
    target_values = []
    for k in initials:
        if initial in k:
            target_values.append(groups_info[k])
    for key in KEYS:
        group_sum[key] = 0.0
    for value in target_values:
        if value == None:
            continue
        if 'solved' in value:
            group_sum['solved'] += 1

            # if '.regression.' in value['solved']:
            #     group_sum['solved reg'] += 1
            if '.initial.' in value['solved']:
                group_sum['1st_analysis_time'] += value['1st_analysis_time']
                continue
        for KEY in KEYS:
            if KEY == 'solved' or KEY == 'solved reg':
                continue
            group_sum[KEY] += value[KEY]
            group_sum[KEY] = round(group_sum[KEY], 2) 
    if (group_sum['anno hits'] + group_sum['abstractions']) == 0:
        group_sum['RR'] = 0.0
    else:
        group_sum['RR'] = round((float) (group_sum['anno hits']) / (group_sum['anno hits'] + group_sum['abstractions']), 2)
    return group_sum

def build_groups_info_dummy_initial(file):
    # inital如果log不全，或者filterlist没有initial，则导致当前统计中缺少该initial
    # 此函数补充生成这个initial
    file_rst = {}
    for key in KEYS:
        file_rst[key] = 0
    file_rst['analysis_time (s)'] = DUMMY_TO
    file_rst['1st_analysis_time'] = file_rst['analysis_time (s)']
    file_rst['solved'] = 'timeout-verification-task'
    return file_rst

def build_groups_info_dummy_timeout(abs, mem, cmd, file):
    # inital如果log不全，或者filterlist没有initial，则导致当前统计中缺少该initial
    # 此函数补充生成这个initial
    file_rst = {}
    for key in KEYS:
        if key == 'solved':
            continue
        file_rst[key] = 0
    # file_rst['abstractions'] = abs
    # file_rst['mem (MB)'] = mem
    if 'arkfb' not in file:
        to155.append(file + '\n')
        # to155.append(file + '\n')
    file_rst['analysis_time (s)'] = DUMMY_TO
    file_rst['solved'] = 'timeout-verification-task'
    return file_rst

no_hit_count = 0
def build_groups_info(isInitialRev, file, file_content):
    file_rst = {}
    abs = 0
    mem = 0
    for i in range(0, len(file_content)):
        line = file_content[i]
        file_rst['RR'] = 0.0
        file_rst['total_time (s)'] = 0.0
        if 'Number of abstractions:' in line:
            abs = file_rst['abstractions'] = extract_int(line.split('(')[0])
        if 'CPU time for analysis' in line:
            file_rst['analysis_time (s)'] = extract_float(line)
        if 'Number of refinements:' in line:# and len(line.split(' '))  == 19:
            file_rst['refinements'] = extract_int(line)
        if 'Used heap memory:' in line:
            mem = file_rst['mem (MB)'] = extract_mem(line)
        if 'Total CPU time for CPAchecker:' in line:
            file_rst['cpu time (s)'] = extract_float(line)
        if 'Number of invariants hits:' in line:
            file_rst['anno hits'] =  extract_int(line.split('(')[0])
        if 'Time for cfa diff:' in line:
            file_rst['cfadiff_time'] =  extract_float(line)
        if 'CPU time for impacted:' in line:
            file_rst['impact_analysis_time'] =  extract_float(line)
        if 'Time for invariant write:' in line:
            file_rst['anno_write_time'] = extract_float(line)
        if 'Time for invariant read:' in line:
            file_rst['anno_read_time'] = extract_float(line)
        if 'Input invariants file size' in line:
            file_rst['anno size'] = extract_int(line)
        if 'CPU time for init:' in line:
            file_rst['anno_reuse_time'] = extract_float(line)
            file_rst['analysis_time* (s)'] = file_rst['analysis_time (s)'] - file_rst['anno_reuse_time']
            if 'anno hits' in file_rst and file_rst['anno hits'] == 0:
                file_rst['anno_reuse_time'] = 0
        if 'Verification result: UNKNOWN' in line or 'Verification result: TIMEOUT' in line:
            if 'Verification result: TIMEOUT' in line:
                print('TIMEOUT:', file)
            if '.initial.' in file:
                file_rst = build_groups_info_dummy_initial(file)
                return abs, mem, file_rst
            else:
                file_rst = build_groups_info_dummy_timeout(abs, mem, cmd,file)
                return abs, mem, file_rst

    if 'analysis_time (s)' in file_rst and 'cfadiff_time' in file_rst:
        file_rst['cpu time (s)'] = file_rst['analysis_time (s)'] + file_rst['cfadiff_time']
    elif 'analysis_time (s)' in file_rst and 'cfadiff_time' not in file_rst:
        file_rst['cpu time (s)'] = file_rst['analysis_time (s)']
    # if ('cpu time (s)' not in file_rst.keys()) and '.initial.' in file:
    if ('cpu time (s)' not in file_rst.keys()) and '.initial.' in file:
        file_rst['cpu time (s)'] = 0
        file_rst['abstractions'] = 0
        pool_initial.append(file)
        file_rst = build_groups_info_dummy_initial(file)
        return abs, mem, file_rst
    if 'cpu time (s)' not in file_rst.keys():
        file_rst = build_groups_info_dummy_timeout(abs, mem, cmd,file)
        return abs, mem, file_rst
    global no_hit_count
    if 'anno hits' not in file_rst or file_rst['anno hits'] == 0 and 'initial' not in file:
        no_hit_count += 1
    target = file_rst['cpu time (s)']
    if target < file_rst['analysis_time (s)']:
        return abs, mem, None
    if target >= TOTALCPUTH or file_rst['analysis_time (s)'] >= 300.00:
        if '.initial.' in file:
            file_rst['cpu time (s)'] = 0
            file_rst['abstractions'] = 0
            pool_initial.append(file)
            file_rst = build_groups_info_dummy_initial(file)
            return abs, mem, file_rst
        file_rst = build_groups_info_dummy_timeout(abs, mem, cmd,file)
        return abs, mem, file_rst
    if file_rst['mem (MB)'] >= 10000:
        print('exceed max 10GB memory')
        return abs, mem, None
    
    if isInitialRev:
        file_rst['1st_analysis_time'] = file_rst['analysis_time (s)']
    # padding null keys
    keys = file_rst.keys()
    for key in KEYS:
        if key not in keys:
            file_rst[key] = 0
    
    file_rst['solved'] = file

    # file_rst['solved reg'] = file
    if (file_rst['anno hits'] + file_rst['abstractions']) != 0:
        file_rst['RR'] = round((float) (file_rst['anno hits']) / (file_rst['anno hits'] + file_rst['abstractions']), 2)
    file_rst['total_time (s)'] = file_rst['analysis_time (s)'] + file_rst['cfadiff_time']
    return abs, mem, file_rst

if __name__ == '__main__':
    groups_info = {}
    groups_sum = {}
    total_sum = {}
    allSumLess = 0
    to155 = []
    for initial in groups.keys():
        isInitialRev = True
        countRev = 0
        countLess = 0
        for file in groups[initial]:
            if not file.endswith('log'):
                continue
            countRev += 1
            groups_info[file] = {}
            (groups_info[file])['solved'] = (file)
            content = open(os.path.join(rst_base, file), 'r').readlines()
            abs = 0
            mem = 0
            cmd = content[0]
            if '.initial' not in file and isInitialRev and not is_all_revs:
                hander = file.split('.')[2] + '.' + file.split('.')[3]
                for f in bak_files:
                    if hander in f and 'initial' in f:
                        groups_info[file] = build_groups_info_dummy_initial(file) 
                        countRev-=1
                        break
            else:
                abs, mem, groups_info[file] = build_groups_info(isInitialRev, file, content)

            if groups_info[file] == None and '.regression.' in file:
                groups_info[file] = build_groups_info_dummy_timeout(abs, mem, cmd,file)
                countRev-=1
                countLess += 1
            if groups_info[file] != None and groups_info[file]['solved'] != 'timeout-verification-task':
                valid_files.append(file)
                if '.regression.' in file:
                    valid_reg_files.append(file)
            isInitialRev = False
        groups_sum[initial] = build_groups_sum(countRev, countLess, initial, groups_info)
        allSumLess += countLess

    total_sum = build_total_sum(groups_sum)
    writer = open(selector + '.csv', 'w')

    write_groups_sum(writer, groups_sum)
    if not is_all_revs:
        write_total_sum(writer, total_sum)
    writer.close()

    selector_suffix = '-' + str(len(raw_initials) + len(valid_reg_files)) + '-' + str(len(valid_reg_files))
    qty_str = selector.split('.')[0] + selector_suffix + '.txt'
    writer = open(qty_str, 'w')
    for file in valid_reg_files:
        writer.write(logname2progname(file) + '\n')
    for file in raw_initials:
        writer.write(logname2progname(file) + '\n')
    writer.close()

    selector_suffix_reg = '-' + str(len(valid_reg_files))
    qty_str_reg = selector.split('.')[0] + selector_suffix_reg + '.txt'
    writer = open(qty_str_reg, 'w')
    for file in valid_reg_files:
        writer.write(logname2progname(file) + '\n')
    writer.close()

    selector_suffix_reg = '-' + str(len(valid_reg_files))
    qty_str_reg = selector.split('.')[0] + selector_suffix_reg + '-full.txt'
    writer = open(qty_str_reg, 'w')
    for file in valid_reg_files:
        writer.write((file) + '\n')
    writer.close()
