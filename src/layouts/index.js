import React from 'react'
import Link from 'gatsby-link'
import { fontFace, injectGlobal } from "emotion"
import styled from "react-emotion"

injectGlobal`
  * {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
  }

  body {
    background-color: #f4f5f6;
    color: #0a2e6b;
    font-family: proxima-nova, Nunino, sans-serif;
  }

  main h1, h2, h3 {
    font-family: Menlo,Monaco,Lucida Console,Liberation Mono,DejaVu Sans Mono,Bitstream Vera San;
    font-weight: 400;
    margin: 60px 0 30px;
    text-rendering: geometricPrecision;
  }

  main h1::before {
    content: '# ';
    color: rgba(0, 0, 0, 0.5);
  }

  h2::before {
    content: '## ';
    color: rgba(0, 0, 0, 0.5);
  }

  h3::before {
    content: '### ';
    color: rgba(0, 0, 0, 0.5);
  }

  p, ul {
    font-size: 14pt;
    line-height: 1.55;
    margin: 22px 0;
  }

  li {
    margin-left: 20px;
  }

  pre, code {
    font-size: 11pt;
  }

  a {
    text-decoration: none;
  }

  ::selection {
    color: #e0e0e0;
    background-color: #073642;
  }
`

const Header = styled.header`
  margin: 3vw auto;
  display: flex;
  justify-content: center;
`;

const Main = styled.main`
  max-width: 1000px;
  margin: auto;
`;

const Monic = styled.span`
  font-weight: 400;
  letter-spacing: 2px;
`;

const HeadH1 = styled.h1`
  font-family: Nunino, sans-serif;
  font-weight: 300;
  margin-top: 0;
  margin-bottom: 100px;
`;

require("./theme.css");

export default class Template extends React.Component {
  render() {
    const { children } = this.props

    return (
      <div>
        <Header>
          <HeadH1>
            <Link
              style={{
                boxShadow: 'none',
                textDecoration: 'none',
                color: 'inherit',
              }}
              to="/"
            >
              <Monic>MONIC</Monic>
              {' '}
              Blog
            </Link>
          </HeadH1>
        </Header>
        <Main>{children()}</Main>
      </div>
    )
  }
}
