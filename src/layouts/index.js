import React from 'react'
import Link from 'gatsby-link'
import { fontFace, injectGlobal } from "emotion"
import styled from "react-emotion"

require("./theme.css");

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
    font-family: proxima-nova, Nunino, sans-serif;
    font-weight: 300;
    margin: 60px 0 30px;
    text-rendering: geometricPrecision;
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

  main a, main button {
    color: #0a2e6b;
    text-decoration: none;
    cursor: pointer;
    border: none;
    padding: 0;
    border-bottom: 1px solid rgba(252,51,89,0.4);
    display: inline-block;
    height: 24px;
    background-color: transparent;
    transition: 0.48s border-bottom-color ease-out;
  }

  main a:hover, main button:hover {
    border-bottom-color: #FC3359;
  }

  main a:hover, main a:active,
  main button:hover, main button:active {
    outline: none;
    transition-duration: 0s;
  }

  ::selection {
    color: #e0e0e0;
    background-color: #073642;
  }
`

const Header = styled.header`
  margin: 3vw auto;
  padding-left: 3vw;
  padding-right: 3vw;
  display: flex;
  justify-content: center;
  width: auto;
  max-width: 1280px;
`;

const HeaderBoxLeft = styled.div`
  flex: 1 1 0px;
  margin-bottom: 100px;
`;

const HeaderBoxRight = styled.div`
  flex: 1 1 0px;
  text-align: right;
  justify-content: flex-end;
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
  font-family: europa, Nunino, sans-serif;
  font-weight: 700;
  font-style: normal;
  font-size: 20px;
  letter-spacing: .04em;
  text-transform: none;
  line-height: 1em;
`;

const HeadItem = styled.div`
  display: inline-block;
  font-family: Arial,Helvetica,sans-serif;
  font-weight: 400;
  font-style: normal;
  font-size: 16px;
  letter-spacing: .05em;
  text-transform: none;
  line-height: 1em;
  text-rendering: optimizeLegibility;
  box-flex: 1;
  flex: 1 1 0px;
`;

const HeadLink = styled.a`
  text-decoration: none;
  color: #0a2e6b;
`;

export default class Template extends React.Component {
  render() {
    const { children } = this.props

    return (
      <div>
        <Header>
          <HeaderBoxLeft>
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
              </Link>
            </HeadH1>
          </HeaderBoxLeft>
          <HeaderBoxRight>
            <HeadItem>
              <HeadLink href="https://www.monic.co/about">About</HeadLink>
            </HeadItem>
            <HeadItem style={{marginLeft: '18px'}}>
              <HeadLink href="/">Blog</HeadLink>
            </HeadItem>
            <HeadItem style={{marginLeft: '18px'}}>
              <HeadLink href="https://www.monic.co/contact">Contact</HeadLink>
            </HeadItem>
          </HeaderBoxRight>
        </Header>
        <Main>{children()}</Main>
      </div>
    )
  }
}
