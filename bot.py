import requests
import pdfplumber
import io
import time
import json
import re
import os
import html
import smtplib
import unicodedata
from email.mime.text import MIMEText
from datetime import datetime, timezone, timedelta
from urllib.parse import urljoin
from playwright.sync_api import sync_playwright
from bs4 import BeautifulSoup

# Fuso horário de Brasília/RN (UTC-3)
FUSO_BRT = timezone(timedelta(hours=-3))

# --- ESTRUTURA DE BUSCA ---
# Configure via variável de ambiente/Secret PESSOAS_PARA_BUSCAR (JSON), ex:
# [{"nome": "Nome Completo", "matricula": "1234567", "cpf": "00011122233"}]
PESSOAS_PARA_BUSCAR = [
          {"nome": "Frederico Augusto Leite Lins", "matricula": "2491940", "cpf": ""},
          {"nome": "Larissa Valdeci da Costa Silva", "matricula": "2545691", "cpf": ""}
        ]



def carregar_pessoas_para_buscar():
    """Carrega a lista de pessoas da variável de ambiente PESSOAS_PARA_BUSCAR (JSON) ou usa a lista local."""
    env_pessoas = os.environ.get("PESSOAS_PARA_BUSCAR", "").strip()
    if env_pessoas:
        try:
            dados = json.loads(env_pessoas)
            if isinstance(dados, list):
                return dados
            print("Aviso: PESSOAS_PARA_BUSCAR deve ser uma lista JSON.")
        except json.JSONDecodeError as e:
            print(f"Erro ao interpretar PESSOAS_PARA_BUSCAR: {e}")
    return PESSOAS_PARA_BUSCAR


def normalizar_texto(texto):
    """Remove acentos/diacríticos e converte para minúsculas."""
    if not texto:
        return ""
    nfkd = unicodedata.normalize('NFKD', texto)
    sem_acentos = ''.join(c for c in nfkd if not unicodedata.combining(c))
    return sem_acentos.lower()


def tokenizar(texto):
    """Extrai tokens alfanuméricos normalizados de uma string."""
    return re.findall(r'[a-z0-9]+', normalizar_texto(texto))


def _mesma_linha(wa, wb):
    tol_y = max(4.0, 0.6 * min(wa['height'], wb['height']))
    return abs(wb['top'] - wa['top']) <= tol_y


def _tem_palavra_entre_na_linha(words, idx_a, idx_b):
    wa, wb = words[idx_a], words[idx_b]
    for k, wk in enumerate(words):
        if k == idx_a or k == idx_b:
            continue
        if _mesma_linha(wa, wk) and wk['x0'] > wa['x1'] - 2.0 and wk['x1'] < wb['x0'] + 2.0:
            return True
    return False


def _eh_proximo_adjacente(words, idx_a, idx_b, anchor_x0):
    """
    Verifica se `words[idx_b]` é imediatamente adjacente a `words[idx_a]` na ordem de leitura
    dentro da mesma coluna ou célula de tabela (mesma linha ou quebra de linha imediata).
    """
    wa, wb = words[idx_a], words[idx_b]

    # Caso 1: mesma linha, logo à direita, sem palavras no meio
    if _mesma_linha(wa, wb):
        gap = wb['x0'] - wa['x1']
        max_gap = max(25.0, 3.5 * wa['height'])
        if -2.0 <= gap <= max_gap and not _tem_palavra_entre_na_linha(words, idx_a, idx_b):
            return True

    # Caso 2: quebra de linha imediata dentro da mesma coluna/célula
    dy = wb['top'] - wa['top']
    max_dy = max(18.0, 2.5 * wa['height'])
    if 2.0 < dy <= max_dy:
        if wb['x0'] >= anchor_x0 - 30.0 and wb['x0'] <= wa['x1'] + 5.0:
            for k, wk in enumerate(words):
                if k == idx_a or k == idx_b:
                    continue
                if _mesma_linha(wa, wk) and -2.0 <= (wk['x0'] - wa['x1']) <= 10.0:
                    return False
                if _mesma_linha(wb, wk) and -2.0 <= (wb['x0'] - wk['x1']) <= 10.0:
                    return False
            return True

    return False


def buscar_nome_em_words(palavras_alvo, words):
    """
    Busca o nome completo de forma espacialmente contígua nas palavras extraídas do PDF.
    Suporta múltiplas colunas, células de tabela, acentuação, hifenização em quebra de linha
    (ex: 'OLI-' + 'VEIRA') e separação por kerning (ex: 'Gran' + 'de').
    Retorna o trecho encontrado ou None.
    """
    if not palavras_alvo or not words:
        return None

    n = len(words)
    w_tokens = [tokenizar(w['text']) for w in words]
    alvo0 = palavras_alvo[0]

    for i in range(n):
        toks_i = w_tokens[i]
        if not toks_i:
            continue

        for start_sub in range(len(toks_i)):
            # Suporta primeiro token completo ou partido por kerning na mesma linha (gap ~ 0)
            matched_indices = [i]
            cur_idx = i
            sub_idx = start_sub + 1
            alvo_idx = 1

            if toks_i[start_sub] != alvo0:
                # Verifica junção de kerning no primeiro token (apenas se for o último sub-token de i)
                if start_sub == len(toks_i) - 1 and alvo0.startswith(toks_i[start_sub]):
                    juntou = False
                    for j in range(n):
                        if j != i and w_tokens[j] and _mesma_linha(words[i], words[j]):
                            if -1.5 <= (words[j]['x0'] - words[i]['x1']) <= 1.5:
                                if toks_i[start_sub] + w_tokens[j][0] == alvo0:
                                    matched_indices.append(j)
                                    cur_idx = j
                                    sub_idx = 1
                                    juntou = True
                                    break
                    if not juntou:
                        continue
                else:
                    continue

            anchor_x0 = words[i]['x0']
            ok = True

            while alvo_idx < len(palavras_alvo):
                if sub_idx < len(w_tokens[cur_idx]):
                    if w_tokens[cur_idx][sub_idx] == palavras_alvo[alvo_idx]:
                        sub_idx += 1
                        alvo_idx += 1
                        continue
                    ok = False
                    break

                alvo_atual = palavras_alvo[alvo_idx]
                found_next = False

                for j in range(n):
                    if j == cur_idx or not w_tokens[j]:
                        continue
                    if not _eh_proximo_adjacente(words, cur_idx, j, anchor_x0):
                        continue

                    # Caso normal: próximo token bate exatamente
                    if w_tokens[j][0] == alvo_atual:
                        cur_idx = j
                        sub_idx = 1
                        alvo_idx += 1
                        matched_indices.append(j)
                        found_next = True
                        break

                    # Caso hifenização em quebra de linha (ex: "OLI-" + "VEIRA") ou kerning
                    eh_hifen = words[j]['text'].endswith('-') and len(w_tokens[j]) == 1
                    if eh_hifen and alvo_atual.startswith(w_tokens[j][0]):
                        for k in range(n):
                            if k == j or k == cur_idx or not w_tokens[k]:
                                continue
                            if _eh_proximo_adjacente(words, j, k, anchor_x0):
                                if w_tokens[j][0] + w_tokens[k][0] == alvo_atual:
                                    cur_idx = k
                                    sub_idx = 1
                                    alvo_idx += 1
                                    matched_indices.extend([j, k])
                                    found_next = True
                                    break
                        if found_next:
                            break

                    # Caso kerning sem hífen na mesma linha (ex: "Gran" + "de")
                    if len(w_tokens[j]) == 1 and alvo_atual.startswith(w_tokens[j][0]):
                        for k in range(n):
                            if k == j or k == cur_idx or not w_tokens[k]:
                                continue
                            if _mesma_linha(words[j], words[k]) and -1.5 <= (words[k]['x0'] - words[j]['x1']) <= 1.5:
                                if w_tokens[j][0] + w_tokens[k][0] == alvo_atual:
                                    cur_idx = k
                                    sub_idx = 1
                                    alvo_idx += 1
                                    matched_indices.extend([j, k])
                                    found_next = True
                                    break
                        if found_next:
                            break

                if not found_next:
                    ok = False
                    break

            if ok:
                # Monta um pequeno trecho de contexto ao redor do achado
                idx_min = max(0, min(matched_indices) - 3)
                idx_max = min(n, max(matched_indices) + 4)
                return ' '.join(words[k]['text'] for k in range(idx_min, idx_max))

    return None


def buscar_inscricao_na_pagina(valor, texto_pagina_norm):
    """Busca matrícula ou inscrição (com ou sem pontuação, ex: 2491940 ou 249.194-0) respeitando fronteiras numéricas."""
    if not valor or not texto_pagina_norm:
        return False
    digitos = re.sub(r'\D', '', str(valor))
    if digitos.isdigit() and len(digitos) >= 6 and str(valor).strip().isdigit():
        padrao = rf'(?<!\d){re.escape(digitos[:-4])}\.?{re.escape(digitos[-4:-1])}-?{re.escape(digitos[-1])}(?!\d)'
        return re.search(padrao, texto_pagina_norm) is not None
    val_norm = normalizar_texto(str(valor)).strip()
    if not val_norm:
        return False
    padrao = r'(?<!\d)' + re.escape(val_norm) + r'(?!\d)'
    return re.search(padrao, texto_pagina_norm) is not None


def buscar_cpf_na_pagina(cpf, texto_pagina_norm):
    """Busca o CPF (com ou sem pontuação) respeitando fronteiras numéricas."""
    if not cpf or not texto_pagina_norm:
        return False
    digitos = re.sub(r'\D', '', cpf)
    if len(digitos) == 11:
        padrao_pontuado = rf'(?<!\d){digitos[0:3]}\.?{digitos[3:6]}\.?{digitos[6:9]}-?{digitos[9:11]}(?!\d)'
        return re.search(padrao_pontuado, texto_pagina_norm) is not None
    padrao = r'(?<!\d)' + re.escape(normalizar_texto(cpf).strip()) + r'(?!\d)'
    return re.search(padrao, texto_pagina_norm) is not None


def processar_pdf(url_pdf, titulo_diario, session, historico):
    print(f"\n--- Processando: {titulo_diario} ---")
    print(f"URL: {url_pdf}")

    try:
        if url_pdf in historico:
            print("PDF já processado anteriormente. Pulando.")
            return []

        print("Baixando PDF...")
        response = session.get(url_pdf, timeout=120)
        response.raise_for_status()

        achados_do_pdf = []

        print("Abrindo PDF com pdfplumber...")
        with pdfplumber.open(io.BytesIO(response.content)) as pdf:
            print(f"O PDF tem {len(pdf.pages)} páginas.")

            for i, pagina in enumerate(pdf.pages):
                texto_da_pagina = pagina.extract_text() or ""
                words = pagina.extract_words(x_tolerance=2, y_tolerance=3)

                if not texto_da_pagina and not words:
                    continue

                texto_da_pagina_norm = normalizar_texto(texto_da_pagina).replace('\n', ' ')

                pessoas = carregar_pessoas_para_buscar()
                for pessoa in pessoas:
                    nome_completo = pessoa['nome']
                    matricula = pessoa.get('matricula') or pessoa.get('inscricao', '')
                    cpf = pessoa.get('cpf', '')
                    palavras_nome = tokenizar(nome_completo)

                    trecho_encontrado = buscar_nome_em_words(palavras_nome, words)
                    nome_encontrado = trecho_encontrado is not None
                    matricula_encontrada = buscar_inscricao_na_pagina(matricula, texto_da_pagina_norm)
                    cpf_encontrado = buscar_cpf_na_pagina(cpf, texto_da_pagina_norm)

                    if nome_encontrado or matricula_encontrada or cpf_encontrado:
                        print(f"ENCONTRADO! {nome_completo} na página {i + 1}")
                        achados_do_pdf.append({
                            'pessoa': pessoa,
                            'pagina': i + 1,
                            'url_pdf': url_pdf,
                            'titulo_diario': titulo_diario,
                            'nome_encontrado': nome_encontrado,
                            'matricula_encontrada': matricula_encontrada,
                            'cpf_encontrado': cpf_encontrado,
                            'trecho': trecho_encontrado or "",
                        })

        print(f"Processamento concluído. Achados: {len(achados_do_pdf)}")
        return achados_do_pdf

    except Exception as e:
        print(f"Erro ao processar o PDF {url_pdf}: {e}")
        return []

def enviar_email_de_alerta(corpo_email):
    remetente = os.environ.get("EMAIL_REMETENTE")
    senha = os.environ.get("EMAIL_SENHA")
    destinatario = os.environ.get("EMAIL_DESTINATARIO")

    if not all([remetente, senha, destinatario]):
        print("Credenciais de e-mail não configuradas. Alerta não enviado.")
        return

    msg = MIMEText(corpo_email, 'html')
    msg['Subject'] = "Alerta de Monitoramento - Diário Oficial RN"
    msg['From'] = remetente
    msg['To'] = destinatario

    try:
        print("Conectando ao servidor de e-mail...")
        with smtplib.SMTP_SSL('smtp.gmail.com', 465) as smtp_server:
            smtp_server.login(remetente, senha)
            smtp_server.sendmail(remetente, destinatario, msg.as_string())
        print("E-mail de alerta enviado com sucesso!")
    except Exception as e:
        print(f"Erro ao enviar e-mail: {e}")

def buscar_edicoes_extras(session, historico):
    """Busca edições extras do diário oficial"""
    print("\n=== BUSCANDO EDIÇÕES EXTRAS ===")
    achados_extras = []
    
    try:
        url_base = "https://www.diariooficial.rn.gov.br/dei/dorn3/"
        print("Acessando página de edições extras...")
        response = session.get(url_base, timeout=30)
        response.raise_for_status()
        
        soup = BeautifulSoup(response.content, 'html.parser')
        links_encontrados = 0
        
        for link in soup.find_all('a'):
            texto_do_link = link.get_text(strip=True)
            if "Edição Extra" in texto_do_link:
                links_encontrados += 1
                href = link.get('href')
                print(f"Link encontrado: {texto_do_link}")
                
                if href:
                    url_extra = urljoin(url_base, href)
                    if url_extra.lower().endswith('.pdf'):
                        achados_extras.extend(processar_pdf(url_extra, texto_do_link, session, historico))
        
        print(f"Total de links de edições extras encontrados: {links_encontrados}")
        
    except Exception as e:
        print(f"Erro ao buscar edições extras: {e}")
    
    return achados_extras

def buscar_edicao_do_dia(session, historico):
    """Busca a edição do dia usando Playwright"""
    print("\n=== BUSCANDO EDIÇÃO DO DIA ===")
    achados_do_dia = []
    
    with sync_playwright() as p:
        try:
            print("Iniciando browser...")
            browser = p.chromium.launch(headless=True)
            page = browser.new_page()
            
            pdf_url_interceptada = None
            
            def interceptar_requisicao(request):
                nonlocal pdf_url_interceptada
                if "cepebr-prod.s3.sa-east-1.amazonaws.com" in request.url and request.url.endswith(".pdf"):
                    pdf_url_interceptada = request.url.split('?')[0]
                    print(f"PDF interceptado: {pdf_url_interceptada}")
            
            page.on("request", interceptar_requisicao)
            
            data_hoje_obj = datetime.now(FUSO_BRT)
            data_hoje_url = data_hoje_obj.strftime('%d-%m-%Y')
            titulo_diario_dia = f"Diário Oficial do Dia {data_hoje_obj.strftime('%d/%m/%Y')}"
            
            url_visualizador = f"https://deirn.sdoe.com.br/diariooficialweb/#/visualizar-jornal?dataPublicacao={data_hoje_url}&diario=MTIx&extra=false"
            print(f"Acessando: {url_visualizador}")
            
            page.goto(url_visualizador, timeout=90000)
            
            # Aguarda interceptar o PDF
            for i in range(20):
                if pdf_url_interceptada: 
                    break
                page.wait_for_timeout(1000)
            
            browser.close()
            
            if pdf_url_interceptada:
                print(f"PDF do dia encontrado.")
                achados_do_dia.extend(processar_pdf(pdf_url_interceptada, titulo_diario_dia, session, historico))
            else:
                print("PDF do dia não foi interceptado.")
                
        except Exception as e:
            print(f"Erro com o Playwright: {e}")
    
    return achados_do_dia

def main():
    print("=== INICIANDO BOT DE MONITORAMENTO ===")
    
    # Carrega histórico
    try:
        with open("historico_alertas.json", "r") as f:
            historico = set(json.load(f))
        print(f"Histórico carregado: {len(historico)} PDFs já processados")
    except FileNotFoundError:
        historico = set()
        print("Nenhum histórico encontrado. Iniciando do zero.")

    session = requests.Session()
    todos_os_achados = []

    # 1. Busca edições extras
    todos_os_achados.extend(buscar_edicoes_extras(session, historico))

    # 2. Busca edição do dia
    todos_os_achados.extend(buscar_edicao_do_dia(session, historico))

    print(f"\n=== RESUMO FINAL ===")
    print(f"Total de achados novos: {len(todos_os_achados)}")

    if not todos_os_achados:
        print("Nenhum novo alerta encontrado. Encerrando.")
        return

    # Monta e envia o e-mail
    corpo_email = "<h1>🚨 Alerta de Monitoramento do Diário Oficial RN</h1>"
    corpo_email += f"<p><strong>Data/Hora:</strong> {datetime.now(FUSO_BRT).strftime('%d/%m/%Y às %H:%M:%S')}</p>"
    
    novos_pdfs_processados = set()
    
    achados_por_pessoa = {}
    for achado in todos_os_achados:
        nome_pessoa = achado['pessoa']['nome']
        if nome_pessoa not in achados_por_pessoa:
            achados_por_pessoa[nome_pessoa] = []
        achados_por_pessoa[nome_pessoa].append(achado)

    for nome_pessoa, lista_de_achados in achados_por_pessoa.items():
        corpo_email += f"<hr><h2>📋 Resultados para: {nome_pessoa}</h2>"
        for achado in lista_de_achados:
            pagina = achado['pagina']
            url_pdf = achado['url_pdf']
            titulo_diario = achado['titulo_diario']

            identificadores = []
            if achado['nome_encontrado']: identificadores.append("NOME")
            if achado['matricula_encontrada']: identificadores.append("MATRÍCULA")
            if achado['cpf_encontrado']: identificadores.append("CPF")

            trecho_html = ""
            if achado.get('trecho'):
                trecho_html = f"<p><strong>📝 Trecho:</strong> <em>...{html.escape(achado['trecho'])}...</em></p>"
            
            corpo_email += f"""
            <div style="background: #e6f2ff; padding: 15px; margin: 10px 0; border-left: 4px solid #007bff; border-radius: 4px;">
                <p><strong>📄 Fonte:</strong> {titulo_diario}</p>
                <p><strong>🔍 Itens Encontrados:</strong> {', '.join(identificadores)}</p>
                <p><strong>📖 Página:</strong> {pagina}</p>
                {trecho_html}
                <p><strong>🔗 Link:</strong> <a href="{url_pdf}" target="_blank">Abrir Diário Oficial</a></p>
            </div>
            """
            novos_pdfs_processados.add(url_pdf)

    corpo_email += "<hr><p><em>Este é um alerta automático do sistema de monitoramento.</em></p>"

    print("Enviando e-mail...")
    enviar_email_de_alerta(corpo_email)

    # Atualiza e salva histórico
    historico.update(novos_pdfs_processados)
    with open("historico_alertas.json", "w") as f:
        json.dump(list(historico), f, indent=2)
    
    print(f"Histórico atualizado: {len(historico)} PDFs processados no total")
    print("=== BOT FINALIZADO ===")

if __name__ == "__main__":
    main()
